/**
 * Run the full extraction pipeline: Charon -> Aeneas -> Tweaks.
 */

import fs from "node:fs";
import path from "node:path";
import chalk from "chalk";
import { findBinary, findProjectRoot, readAeneasRev } from "./lib/paths.js";
import { run, runStreaming } from "./lib/shell.js";
import { syncLeanToolchain } from "./lib/lean-toolchain.js";

// ── Translation configuration ─────────────────────────────────────────

/** The Rust crate directory (relative to the project root) and its charon crate name. */
const CRATE_DIR = "curve25519-dalek";
const CRATE_NAME = "curve25519_dalek";

/** Charon preset and the per-target triples (build.rs derives `curve25519_dalek_bits`). */
const CHARON_PRESET = "aeneas";
const CHARON_TARGETS = [
  "x86_64-unknown-linux-gnu", // -> curve25519_dalek_bits="64"
  "i686-unknown-linux-gnu",   // -> curve25519_dalek_bits="32"
];
/** rustc cfg overrides for the charon build only (via CARGO_ENCODED_RUSTFLAGS). */
const CHARON_RUSTFLAGS = ['--cfg=curve25519_dalek_backend="serial"'];

/** Aeneas CLI options (each rendered as `-<opt>`); Lean backend is always used. */
const AENEAS_OPTIONS = ["split-files", "emit-json"];

/** Lean output root and the sub-dir that becomes the module prefix (`Curve25519Dalek.*`). */
const DEST = "curve25519-dalek/lean";
const SUBDIR = "Curve25519Dalek";

/** Files Aeneas must produce (basenames under the output dir); used to detect a failed run. */
const GENERATED_FILES = ["Funs.lean", "Types.lean", "FunsExternal_Template.lean", "TypesExternal_Template.lean"];

/**
 * True if `binPath` is an ELF whose program interpreter lives in the Nix store
 * (i.e. a Nix-built binary). `make setup-charon` builds Charon via `nix build`,
 * producing binaries linked against the Nix glibc loader.
 */
function usesNixLoader(binPath: string): boolean {
  try {
    const fd = fs.openSync(binPath, "r");
    const buf = Buffer.alloc(4096);
    fs.readSync(fd, buf, 0, buf.length, 0);
    fs.closeSync(fd);
    return /\/nix\/store\/[^\0]*ld-linux/.test(buf.toString("latin1"));
  } catch {
    return false;
  }
}

/**
 * Locate a Nix-provided `libz.so.1` lib dir. A Nix-built charon-driver uses the
 * Nix glibc loader, whose search path is the Nix store, so it can't see the
 * system libz.so.1 that `librustc_driver` needs — we must put a matching Nix zlib
 * on LD_LIBRARY_PATH. Returns null if none is found.
 */
function findNixZlibLibDir(): string | null {
  const store = "/nix/store";
  let entries: string[];
  try {
    entries = fs.readdirSync(store);
  } catch {
    return null;
  }
  for (const name of entries) {
    if (!name.includes("-zlib-")) continue;
    const libDir = path.join(store, name, "lib");
    if (fs.existsSync(path.join(libDir, "libz.so.1"))) return libDir;
  }
  return null;
}

/** Resolve a binary on the system PATH (via `which`), or null if absent. */
async function whichBin(name: string): Promise<string | null> {
  try {
    return (await run("which", [name], { silent: true })).trim() || null;
  } catch {
    return null;
  }
}

/** The version reported by `aeneas -version` (strips the leading `aeneas `), or null. */
async function aeneasVersion(bin: string): Promise<string | null> {
  try {
    return (await run(bin, ["-version"], { silent: true })).trim().replace(/^aeneas\s+/, "") || null;
  } catch {
    return null;
  }
}

/** True if the reported version identifies the pinned rev (exact or prefix, for short/full SHAs). */
function versionMatches(ver: string, rev: string): boolean {
  return ver === rev || ver.startsWith(rev) || rev.startsWith(ver);
}

/**
 * Choose the charon+aeneas binaries. Prefer an on-PATH aeneas whose `-version` matches
 * the lakefile's pinned rev (using the PATH charon alongside it); otherwise fall back to
 * the bundled `.aeneas/` release. Returns absolute paths for both.
 */
async function resolveToolchain(root: string): Promise<{ charonBin: string; aeneasBin: string }> {
  const rev = readAeneasRev(root);
  const pathAeneas = await whichBin("aeneas");
  if (pathAeneas) {
    const ver = await aeneasVersion(pathAeneas);
    if (ver && versionMatches(ver, rev)) {
      const pathCharon = await whichBin("charon");
      if (pathCharon) {
        console.log(chalk.green(`  Using on-PATH toolchain: aeneas ${ver} matches lakefile rev ${rev}.`));
        return { charonBin: pathCharon, aeneasBin: pathAeneas };
      }
      console.log(chalk.yellow("  On-PATH aeneas matches rev but no charon on PATH; using .aeneas/."));
    }
  }
  const charonBin = findBinary("charon", root);
  const aeneasBin = findBinary("aeneas", root);
  if (!charonBin || !aeneasBin) {
    throw new Error(
      `No matching aeneas for rev ${rev} on PATH, and .aeneas/ is missing binaries. ` +
      `Run 'npm run aeneas-install' first.`,
    );
  }
  console.log(chalk.dim(`  Using bundled .aeneas/ toolchain (lakefile rev ${rev}).`));
  return { charonBin, aeneasBin };
}

async function main(): Promise<void> {
  console.log(chalk.bold("\nAeneas Extract\n"));

  const root = findProjectRoot();

  // Resolve binaries: on-PATH toolchain matching the lakefile rev, else bundled .aeneas/.
  const { charonBin, aeneasBin } = await resolveToolchain(root);

  // Charon reads [package.metadata.charon] from ./Cargo.toml in its cwd,
  // but always outputs the LLBC to the workspace root regardless of cwd.
  const crateDir = path.join(root, CRATE_DIR);
  const llbcFile = `${CRATE_NAME}.llbc`;
  const llbcPath = path.join(root, llbcFile); // charon outputs to workspace root
  const destDir = path.join(root, DEST);
  const outputDir = SUBDIR ? path.join(destDir, SUBDIR) : destDir;
  const logsDir = path.join(root, ".logs");

  // ── Step 1: Charon ──────────────────────────────────────────────────
  console.log(chalk.bold("Step 1: Generating LLBC with Charon..."));

  const charonArgs: string[] = ["cargo"];

  if (CHARON_PRESET) charonArgs.push(`--preset=${CHARON_PRESET}`);

  // Multi-target (build.rs derives curve25519_dalek_bits per target).
  for (const target of CHARON_TARGETS) {
    charonArgs.push("--targets", target);
  }

  // Pin the exact LLBC output path.
  charonArgs.push("--dest-file", llbcPath);

  // Cargo feature selection lives in curve25519-dalek/Cargo.toml `[features] default`,
  // so no `-- <cargo args>` are needed here.

  // Remove stale LLBC
  if (fs.existsSync(llbcPath)) {
    fs.unlinkSync(llbcPath);
  }

  fs.mkdirSync(logsDir, { recursive: true });

  // Force cfg overrides (e.g. the serial u64 backend) for the charon build only,
  // so the crate's normal multi-backend builds are unaffected. CARGO_ENCODED_RUSTFLAGS
  // treats each entry as one flag token (separated by 0x1f), avoiding whitespace splitting.
  const charonEnvParts: Record<string, string> = {};
  if (CHARON_RUSTFLAGS.length > 0) {
    charonEnvParts.CARGO_ENCODED_RUSTFLAGS = CHARON_RUSTFLAGS.join("\x1f");
  }
  // A Nix-built charon-driver (make setup-charon runs `nix build`) uses the Nix
  // glibc loader, which searches the Nix store and can't find the system
  // libz.so.1 that librustc_driver needs. Put a matching Nix zlib on
  // LD_LIBRARY_PATH; Charon forwards this to charon-driver (appending the rustup
  // toolchain lib dir itself). No-op on non-Nix systems.
  if (usesNixLoader(charonBin)) {
    const nixZlibDir = findNixZlibLibDir();
    if (nixZlibDir) {
      charonEnvParts.LD_LIBRARY_PATH = [nixZlibDir, process.env.LD_LIBRARY_PATH]
        .filter(Boolean)
        .join(":");
    } else {
      console.log(chalk.yellow(
        "  Warning: charon is a Nix build but no Nix zlib was found; " +
        "charon-driver may fail to load libz.so.1.",
      ));
    }
  }
  const charonEnv = Object.keys(charonEnvParts).length > 0 ? charonEnvParts : undefined;

  await runStreaming(charonBin, charonArgs, {
    cwd: crateDir,  // read [package.metadata.charon] from crate's Cargo.toml
    env: charonEnv,
    logFile: path.join(logsDir, "charon.log"),
  });

  if (!fs.existsSync(llbcPath)) {
    throw new Error(`Failed to generate ${llbcFile}`);
  }
  console.log(chalk.green(`  LLBC generated: ${llbcFile}\n`));

  // ── Step 2: Aeneas ──────────────────────────────────────────────────
  console.log(chalk.bold("Step 2: Generating Lean files with Aeneas..."));

  const aeneasArgs: string[] = [
    "-backend", "lean",  // we only ever target the Lean backend
    ...AENEAS_OPTIONS.map((o) => `-${o}`),
    "-dest", destDir,
  ];
  if (SUBDIR) {
    aeneasArgs.push("-subdir", SUBDIR);
  }
  aeneasArgs.push(llbcPath);  // absolute path since aeneas runs from root

  fs.mkdirSync(outputDir, { recursive: true });

  // Aeneas may exit non-zero while still producing output (known errors like
  // "join of nested borrows not supported" or internal errors on certain
  // constructs are non-fatal for our codebase).  We check for the output
  // files explicitly rather than relying solely on the exit code.
  try {
    await runStreaming(aeneasBin, aeneasArgs, {
      cwd: root,
      logFile: path.join(logsDir, "aeneas.log"),
    });
  } catch {
    // Check if output files were generated despite the error
    const missingFiles = GENERATED_FILES.filter(
      (f) => !fs.existsSync(path.join(outputDir, f)),
    );
    if (missingFiles.length > 0) {
      throw new Error(
        `Aeneas failed and did not generate: ${missingFiles.join(", ")}. See .logs/aeneas.log`,
      );
    }
    console.log(chalk.yellow("  Aeneas exited with errors but output files were generated (see .logs/aeneas.log)\n"));
  }

  console.log(chalk.green(`  Lean files generated in ${path.relative(root, outputDir)}/\n`));

  // ── Step 3: Regenerate hand-imported External files from templates ───
  const externalRegen = [
    {
      template: "FunsExternal_Template.lean",
      target: "FunsExternal.lean",
      importAnchor: "import Curve25519Dalek.Types",
      importLine: "import Subtle",
    },
    {
      template: "TypesExternal_Template.lean",
      target: "TypesExternal.lean",
      importAnchor: "import Aeneas",
      importLine: "import Subtle.Types",
    },
  ];
  console.log(chalk.bold("Step 3: Regenerating External files..."));
  for (const rule of externalRegen) {
    const templatePath = path.join(outputDir, rule.template);
    const targetPath = path.join(outputDir, rule.target);
    if (!fs.existsSync(templatePath)) {
      console.log(
        chalk.yellow(`  Warning: template not found, skipping: ${rule.template}`),
      );
      continue;
    }
    const out: string[] = [];
    let skipSubtle = false;
    for (const line of fs.readFileSync(templatePath, "utf8").split("\n")) {
      if (line === "-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS") continue;
      if (line.startsWith("-- This is a template file: rename it")) continue;
      if (/^\s*\/-- \[subtle::/.test(line)) {
        skipSubtle = true;
        continue;
      }
      if (/^\s*\/--/.test(line)) skipSubtle = false; // a non-subtle doc block begins
      if (skipSubtle) continue;
      out.push(line);
      if (line === rule.importAnchor) out.push(rule.importLine);
    }
    fs.writeFileSync(targetPath, out.join("\n"));
    console.log(chalk.green(`  Regenerated ${rule.target}`));
  }
  console.log();

  // ── Step 4: Lean toolchain sync ─────────────────────────────────────
  syncLeanToolchain(root);

  console.log(chalk.green("Done."));
}

main().catch((err) => {
  console.error(chalk.red(`\nError: ${err.message}`));
  process.exit(1);
});
