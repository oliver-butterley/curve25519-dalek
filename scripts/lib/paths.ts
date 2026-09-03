import path from "node:path";
import fs from "node:fs";

/**
 * Resolve a binary from the extracted aeneas release bundle.
 *
 * Bundle layout:
 *   .aeneas/aeneas
 *   .aeneas/charon
 *   .aeneas/charon-driver
 *   .aeneas/rust-toolchain
 *   .aeneas/backends/...
 */
/** Walk up from `from` (default cwd) to the directory containing `lakefile.toml`. */
export function findProjectRoot(from?: string): string {
  let dir = from ?? process.cwd();
  while (true) {
    if (fs.existsSync(path.join(dir, "lakefile.toml"))) return dir;
    const parent = path.dirname(dir);
    if (parent === dir) throw new Error("Could not find lakefile.toml in any parent directory");
    dir = parent;
  }
}

export function findBinary(name: "charon" | "aeneas", root: string): string | null {
  const p = path.join(root, ".aeneas", name);
  return fs.existsSync(p) ? p : null;
}

/**
 * The pinned aeneas revision, read from the `[[require]] name = "aeneas"` block's
 * `rev` in lakefile.toml. This is the single source of truth for which aeneas/charon
 * version to use: `aeneas-install` downloads the release for this tag, and
 * `translate` prefers an on-PATH aeneas whose `-version` reports this rev.
 */
export function readAeneasRev(root: string): string {
  const text = fs.readFileSync(path.join(root, "lakefile.toml"), "utf8");
  const m = text.match(/name\s*=\s*"aeneas"[\s\S]*?\brev\s*=\s*"([^"]+)"/);
  if (!m) throw new Error("Could not find the aeneas `rev` in lakefile.toml");
  return m[1];
}

/** The aeneas repo git URL, read from the `git` of the `aeneas` require in lakefile.toml. */
export function readAeneasGit(root: string): string {
  const text = fs.readFileSync(path.join(root, "lakefile.toml"), "utf8");
  const m = text.match(/name\s*=\s*"aeneas"[\s\S]*?\bgit\s*=\s*"([^"]+)"/);
  if (!m) throw new Error("Could not find the aeneas `git` URL in lakefile.toml");
  return m[1];
}
