module
public import Specs.Lemmas.AsNat
public import Specs.Lemmas.Bitwise
public section

/-! # Lemmas about little-endian byte lists and byte arrays -/

open Aeneas Aeneas.Std

/-- A power of two up to `2 ^ 64` divides the size of `U64`. -/
theorem Aeneas.Std.U64.two_pow_dvd_size {n : ℕ} (hn : n ≤ 64) : 2 ^ n ∣ U64.size := by
  rw [show U64.size = 2 ^ 64 by simp [U64.size, U64.numBits]]
  exact Nat.pow_dvd_pow 2 hn

/-- The little-endian bytes of a bit vector, read in radix `256`, give back its value. -/
theorem BitVec.ofDigits_toLEBytes {w : ℕ} (v : BitVec w) :
    Nat.ofDigits 256 (v.toLEBytes.map BitVec.toNat) = v.toNat := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rw [BitVec.toLEBytes]
    split_ifs with hw
    · have hv := v.isLt
      have hlt : v.toNat / 2 ^ 8 < 2 ^ (w - 8) := by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
        exact lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega))
      simp only [List.map_cons, Nat.ofDigits_cons, ih (w - 8) (by omega), BitVec.toNat_setWidth,
        BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hlt]
      omega
    · have hw0 : w = 0 := by omega
      subst hw0
      simp [BitVec.toNat_of_zero_length]

/-- Copying a list `l` to the front of a zero list. -/
theorem List.setSlice!_replicate_zero {α : Type} (n : ℕ) (z : α) (l : List α)
    (hl : l.length ≤ n) :
    (List.replicate n z).setSlice! 0 l = l ++ List.replicate (n - l.length) z := by
  simp [List.setSlice!, Nat.min_eq_left hl, List.take_of_length_le]

/-- Digit `j` of a number written with digits below `b`. -/
theorem Nat.ofDigits_div_pow_mod (b : ℕ) (L : List ℕ) (hL : ∀ d ∈ L, d < b) (j : ℕ) :
    Nat.ofDigits b L / b ^ j % b = L[j]! := by
  induction L generalizing j with
  | nil => simp
  | cons d L ih =>
    have hd : d < b := hL d List.mem_cons_self
    have hb : 0 < b := by omega
    rw [Nat.ofDigits_cons]
    cases j with
    | zero => simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
    | succ j =>
      rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hb,
        Nat.div_eq_of_lt hd, Nat.zero_add, ih (fun d' hd' => hL d' (List.mem_cons_of_mem _ hd'))]
      simp

/-- The first `k` digits of `x` in radix `b` give `x % b ^ k`. -/
theorem Nat.sum_digits_eq_mod (b k x : ℕ) :
    ∑ j ∈ Finset.range k, b ^ j * (x / b ^ j % b) = x % b ^ k := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih => rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ]

/-- A little-endian byte list read as a bit vector has the value of its digits in radix `256`. -/
theorem BitVec.toNat_fromLEBytes (l : List Byte) :
    (BitVec.fromLEBytes l).toNat = Nat.ofDigits 256 (l.map BitVec.toNat) := by
  induction l with
  | nil => simp [BitVec.fromLEBytes]
  | cons b l ih =>
    have hlt : (BitVec.fromLEBytes l).toNat < 2 ^ (8 * l.length) := (BitVec.fromLEBytes l).isLt
    have hb : b.toNat < 2 ^ 8 := b.isLt
    have hpow : 2 ^ (8 * l.length) * 2 ^ 8 = 2 ^ (8 * (l.length + 1)) := by
      rw [← Nat.pow_add]; ring_nf
    have hlt' : (BitVec.fromLEBytes l).toNat < 2 ^ (8 * (l.length + 1)) :=
      lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hsh : (BitVec.fromLEBytes l).toNat <<< 8 < 2 ^ (8 * (l.length + 1)) := by
      rw [Nat.shiftLeft_eq, ← hpow]
      exact Nat.mul_lt_mul_of_pos_right hlt (by positivity)
    have hb' : b.toNat < 2 ^ (8 * (l.length + 1)) :=
      lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [BitVec.fromLEBytes, BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
      BitVec.toNat_setWidth, List.length_cons, Nat.mod_eq_of_lt hb', Nat.mod_eq_of_lt hlt',
      Nat.mod_eq_of_lt hsh, Nat.or_shiftLeft_eq_add_pow_mul _ hb, ih, List.map_cons,
      Nat.ofDigits_cons]
    rfl

namespace Aeneas.Std.Array

/-- A byte array holding the little-endian bytes of `v` followed by zeros has value `v`. -/
theorem asNat_setSlice!_toLEBytes {n : Usize} (a : Array U8 n) {w : ℕ} (v : BitVec w)
    (hw : (w + 7) / 8 ≤ n.val)
    (h : a.val = (List.replicate n.val 0#u8).setSlice! 0 (v.toLEBytes.map UScalar.mk)) :
    a.asNat 8 = v.toNat := by
  rw [Array.asNat, h, List.setSlice!_replicate_zero _ _ _ (by simpa using hw)]
  have h0 : (0#u8).val = 0 := rfl
  simp only [List.map_append, List.map_replicate, h0, Nat.ofDigits_append_replicate_zero]
  rw [List.map_map]
  exact BitVec.ofDigits_toLEBytes v

end Aeneas.Std.Array

namespace Aeneas.Std.Array

/-- An array whose first `m` digits are those of `b` and whose other digits are zero has the
value of `b`. -/
theorem asNat_eq_of_prefix {ty : UScalarTy} {n m : Usize} (bits : ℕ) (a : Array (UScalar ty) n)
    (b : Array (UScalar ty) m) (hmn : m.val ≤ n.val) (hb : ∀ j < m.val, a[j]!.val = b[j]!.val)
    (hz : ∀ j, m.val ≤ j → j < n.val → a[j]!.val = 0) :
    a.asNat bits = b.asNat bits := by
  rw [asNat_eq_sum, asNat_eq_sum, ← Finset.sum_range_add_sum_Ico _ hmn]
  have h0 : ∑ j ∈ Finset.Ico m.val n.val, 2 ^ (bits * j) * a[j]!.val = 0 :=
    Finset.sum_eq_zero fun j hj => by
      rw [Finset.mem_Ico] at hj
      rw [hz j hj.1 hj.2, Nat.mul_zero]
  rw [h0, Nat.add_zero]
  exact Finset.sum_congr rfl fun j hj => by rw [hb j (Finset.mem_range.mp hj)]

/-- The value modulo `2 ^ (bits * m)` of an array with digits below `2 ^ bits` is given by its first
`m` digits. -/
theorem asNat_mod_pow_eq_sum {ty : UScalarTy} {n : Usize} (bits m : ℕ) (a : Array (UScalar ty) n)
    (hmn : m ≤ n.val) (ha : ∀ j < n.val, a[j]!.val < 2 ^ bits) :
    a.asNat bits % 2 ^ (bits * m) = ∑ j ∈ Finset.range m, 2 ^ (bits * j) * a[j]!.val := by
  have hdvd : 2 ^ (bits * m) ∣ ∑ j ∈ Finset.Ico m n.val, 2 ^ (bits * j) * a[j]!.val :=
    Finset.dvd_sum fun j hj => Dvd.dvd.mul_right
      (Nat.pow_dvd_pow 2 (Nat.mul_le_mul_left _ (Finset.mem_Ico.mp hj).1)) _
  obtain ⟨c, hc⟩ := hdvd
  have hlt := sum_pow_mul_lt bits m (fun j => a[j]!.val) fun j hj => ha j (by omega)
  rw [asNat_eq_sum, ← Finset.sum_range_add_sum_Ico _ hmn, hc, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hlt]

/-- The first `m` digits of an array, with digits below `2 ^ bits`, give its value modulo
`2 ^ (bits * m)`. -/
theorem asNat_mod_of_prefix {ty : UScalarTy} {n m : Usize} (bits : ℕ) (a : Array (UScalar ty) n)
    (b : Array (UScalar ty) m) (hmn : m.val ≤ n.val) (hb : ∀ j < m.val, a[j]!.val = b[j]!.val)
    (ha : ∀ j < n.val, a[j]!.val < 2 ^ bits) :
    a.asNat bits % 2 ^ (bits * m.val) = b.asNat bits := by
  rw [asNat_mod_pow_eq_sum bits m.val a hmn ha, asNat_eq_sum]
  exact Finset.sum_congr rfl fun j hj => by rw [hb j (Finset.mem_range.mp hj)]

/-- Splitting the digits of an array into its first `m` and its last `k` digits. -/
theorem asNat_eq_split {ty : UScalarTy} {n m k : Usize} (bits : ℕ) (a : Array (UScalar ty) n)
    (b : Array (UScalar ty) m) (c : Array (UScalar ty) k) (h : m.val + k.val = n.val)
    (hb : ∀ j < m.val, a[j]!.val = b[j]!.val)
    (hc : ∀ j < k.val, a[m.val + j]!.val = c[j]!.val) :
    a.asNat bits = b.asNat bits + 2 ^ (bits * m.val) * c.asNat bits := by
  rw [asNat_eq_sum, asNat_eq_sum, asNat_eq_sum, ← h, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun j hj => by rw [hb j (Finset.mem_range.mp hj)]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [hc j (Finset.mem_range.mp hj), Nat.mul_add, Nat.pow_add, Nat.mul_assoc]

/-- An array with digits below `2 ^ bits` is below `2 ^ (bits * m)` iff its digits from `m` on
are zero. -/
theorem asNat_lt_pow_iff {ty : UScalarTy} {n : Usize} (bits m : ℕ) (a : Array (UScalar ty) n)
    (hmn : m ≤ n.val) (ha : ∀ j < n.val, a[j]!.val < 2 ^ bits) :
    a.asNat bits < 2 ^ (bits * m) ↔ ∀ j, m ≤ j → j < n.val → a[j]!.val = 0 := by
  rw [asNat_eq_sum, ← Finset.sum_range_add_sum_Ico _ hmn]
  constructor
  · intro hlt j hmj hjn
    by_contra hne
    have hle : 2 ^ (bits * j) * a[j]!.val ≤
        ∑ k ∈ Finset.Ico m n.val, 2 ^ (bits * k) * a[k]!.val :=
      Finset.single_le_sum (f := fun k => 2 ^ (bits * k) * a[k]!.val) (fun _ _ => Nat.zero_le _)
        (Finset.mem_Ico.mpr ⟨hmj, hjn⟩)
    have hpow : 2 ^ (bits * m) ≤ 2 ^ (bits * j) * a[j]!.val :=
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hmj)).trans
        (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne))
    omega
  · intro hz
    have h0 : ∑ k ∈ Finset.Ico m n.val, 2 ^ (bits * k) * a[k]!.val = 0 :=
      Finset.sum_eq_zero fun k hk => by
        rw [Finset.mem_Ico] at hk
        rw [hz k hk.1 hk.2, Nat.mul_zero]
    rw [h0, Nat.add_zero]
    exact sum_pow_mul_lt bits m (fun j => a[j]!.val) fun j hj => ha j (by omega)

/-- Setting digit `k` changes the value by the difference of the digits, weighted by
`2 ^ (bits * k)`. -/
theorem asNat_set_add {ty : UScalarTy} {n : Usize} (bits : ℕ) (a : Array (UScalar ty) n)
    (k : Usize) (x : UScalar ty) (hk : k.val < n.val) :
    (a.set k x).asNat bits + 2 ^ (bits * k.val) * a[k.val]!.val
      = a.asNat bits + 2 ^ (bits * k.val) * x.val := by
  have hmem : k.val ∈ Finset.range n.val := Finset.mem_range.mpr hk
  rw [asNat_eq_sum, asNat_eq_sum, ← Finset.add_sum_erase _ _ hmem,
    ← Finset.add_sum_erase _ _ hmem,
    Array.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, by simpa using hk⟩]
  have hrest : ∑ j ∈ (Finset.range n.val).erase k.val, 2 ^ (bits * j) * (a.set k x)[j]!.val
      = ∑ j ∈ (Finset.range n.val).erase k.val, 2 ^ (bits * j) * a[j]!.val :=
    Finset.sum_congr rfl fun j hj => by
      rw [Array.getElem!_Nat_set_ne _ _ _ _ (Ne.symm (Finset.ne_of_mem_erase hj))]
  rw [hrest]
  ring

/-- Limbs of `8 * bits` bits, each made of the next 8 digits of `b` (and zero limbs above), have the
value of `b`. -/
theorem asNat_limbs_eq {tyL tyB : UScalarTy} {n m : Usize} (bits k : ℕ)
    (L : Array (UScalar tyL) n) (b : Array (UScalar tyB) m) (hm : m.val = 8 * k) (hk : k ≤ n.val)
    (hL : ∀ i < n.val, L[i]!.val < 2 ^ (8 * bits))
    (hLb : ∀ i < k, ∀ j < 8, L[i]!.val / 2 ^ (bits * j) % 2 ^ bits = b[8 * i + j]!.val)
    (hz : ∀ i, k ≤ i → i < n.val → L[i]!.val = 0) :
    L.asNat (8 * bits) = b.asNat bits := by
  rw [asNat_eq_sum_blocks bits 8 k b (by rw [hm]), asNat_eq_sum,
    ← Finset.sum_range_add_sum_Ico _ hk]
  have h0 : ∑ i ∈ Finset.Ico k n.val, 2 ^ (8 * bits * i) * L[i]!.val = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_Ico] at hi
      rw [hz i hi.1 hi.2, Nat.mul_zero]
  rw [h0, Nat.add_zero, Nat.mul_comm 8 bits]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  congr 1
  have hsum := Nat.sum_digits_eq_mod (2 ^ bits) 8 L[i]!.val
  rw [← pow_mul, Nat.mod_eq_of_lt (by rw [Nat.mul_comm]; exact hL i (by omega))] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← pow_mul, hLb i hi' j (Finset.mem_range.mp hj)]

/-- Digit `j` of an array whose digits are below `2 ^ bits`. -/
theorem asNat_div_pow_mod {ty : UScalarTy} {n : Usize} (bits : ℕ) (a : Array (UScalar ty) n)
    (ha : ∀ i < n.val, a[i]!.val < 2 ^ bits) (j : ℕ) :
    a.asNat bits / 2 ^ (bits * j) % 2 ^ bits = a[j]!.val := by
  have hL : ∀ d ∈ a.val.map (·.val), d < 2 ^ bits := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
    simp only [List.length_map, List.getElem_map] at hi ⊢
    have := ha i (by simpa using hi)
    rwa [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some] at this
  rw [Array.asNat, pow_mul, Nat.ofDigits_div_pow_mod _ _ hL j, Array.getElem!_Nat_eq]
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_map]
  by_cases hj : j < a.val.length
  · rw [List.getElem?_eq_getElem hj]
    rfl
  · rw [List.getElem?_eq_none (Nat.not_lt.mp hj), Option.map_none, Option.getD_none,
      Option.getD_none, UScalar.default_val]
    rfl

end Aeneas.Std.Array
