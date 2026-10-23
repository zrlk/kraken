/-
**The runtime's phase facts from the decided table** (AArch64; the
generic part of the consumer glue of `Scc/Cert/Rt/RtPhA64.lean`): a fact
that passes `factOk` with the labels resolved by `code` gives the hand
proofs' form at any label map `lab` agreeing with `code` where it resolves
(`hlab`; the loader's, `label_threadAt_of_codeOf`):

- `blkPh_of_factOk`: `.blk l k b ra dead` gives `blkPh` at
  `lab l + 4 k`, a `ret` returning to `lab r` (`ra = some r`), any dead set
  holding the label `dead`'s address;
- `step_of_factOk`, `ok_of_factOk`, `ne_of_factOk`, `ph_of_factOk`: the
  single-pc facts at `lab l + 4 k`.

The per-function projections (`TcbPh`, `TakePh`, `TiPh`, `SwPh`, `MainPh`)
build on these.
-/
import Scc.Cert.Rt.RtPhA64
import Spike.Lib.A64SegInst

namespace Spike.Lib.A64.Rt.PhOfTab

open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow Spike.Lib.A64Consumer
open Scc.Cert.Rt.A64 (PhFact factOk blkOkN tgtsN deadN pcAt)

variable {code : String → Option Nat} {lab : Label → Int64}

/-- An address `a + o` as a pc: `Int64.ofNat a + Int64.ofNat o` reads
`(a + o) % 2 ^ 64`. -/
theorem toNat_add (a o : Nat) : (Int64.ofNat a + Int64.ofNat o).toBitVec.toNat = (a + o) % 2 ^ 64 := by
  rw [← Int64.ofNat_add]; simp

/-- A resolved label read through `lab`. -/
theorem pcAt_eq (hlab : ∀ l a, code l = some a → lab l = Int64.ofNat a) {l : String} {k t : Nat}
    (h : pcAt code l k = some t) : (lab l + Int64.ofNat (4 * k)).toBitVec.toNat = t := by
  unfold pcAt at h
  cases hc : code l with
  | none => rw [hc] at h; cases h
  | some a => rw [hc] at h; cases h; rw [hlab l a hc, toNat_add]

/-- A resolved label at offset `0`. -/
theorem pcAt0_eq (hlab : ∀ l a, code l = some a → lab l = Int64.ofNat a) {l : String} {t : Nat}
    (h : pcAt code l 0 = some t) : (lab l).toBitVec.toNat = t := by
  have := pcAt_eq hlab h
  rwa [show Int64.ofNat (4 * 0) = 0 from rfl, Int64.add_zero] at this

/-- **An instruction's checked targets are `aiTgts`'** (their pcs), the
return address `lab r`. -/
theorem aiTgts_sub (hlab : ∀ l a, code l = some a → lab l = Int64.ofNat a) {fall : Int64}
    {ra : Option String} {rapc : Int64} (hra : ∀ r, ra = some r → rapc = lab r) {ai : Flow.AI}
    {ts : List Nat} (h : tgtsN code fall.toBitVec.toNat ra ai = some ts) :
    ∀ t ∈ aiTgts lab fall rapc ai, t.toBitVec.toNat ∈ ts := by
  intro t ht
  cases ai with
  | b L | bl L =>
    simp only [tgtsN, aiTgts, List.mem_singleton] at h ht
    obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp h
    subst ht; simp [pcAt0_eq hlab ht']
  | bcond cc L | cbz r L | cbnz r L =>
    simp only [tgtsN, aiTgts, List.mem_cons, List.not_mem_nil, or_false] at h ht
    obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp h
    rcases ht with rfl | rfl
    · simp [pcAt0_eq hlab ht']
    · simp
  | ret x =>
    simp only [tgtsN, aiTgts, List.mem_singleton] at h ht
    cases hr : ra with
    | none => rw [hr] at h; cases h
    | some r =>
      rw [hr] at h
      obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp h
      subst ht; rw [hra r hr, pcAt0_eq hlab ht']; simp
  | _ =>
    simp only [tgtsN, aiTgts, List.mem_singleton, Option.some.injEq] at h ht
    subst ht; subst h; simp

/-- **A checked block passes `blkPh`** at `lab l + 4 k` (`a` the label's
address), a `ret` returning to `rapc` (`lab r` for `ra = some r`), any dead
set holding the label `dead`'s address. -/
theorem blkPh_of_blkOkN (hlab : ∀ l a, code l = some a → lab l = Int64.ofNat a) {okPc : Nat → Bool}
    {ph : Nat → Nat} {l : String} {a k : Nat} (hl : code l = some a) {b : List Directive}
    {ra : Option String} {dead : Option String} {rapc : Int64} (hra : ∀ r, ra = some r → rapc = lab r)
    {dset : Nat → Bool} (hd : ∀ t, deadN code dead t = true → dset t = true)
    (h : blkOkN code okPc ph a k b ra dead = true) :
    blkPh okPc ph dset lab (lab l + Int64.ofNat (4 * k)) rapc b = true := by
  have hpc : ∀ j, (lab l + Int64.ofNat (4 * k) + Int64.ofNat (4 * j)).toBitVec.toNat =
      (a + 4 * (k + j)) % 2 ^ 64 := by
    intro j
    rw [hlab l a hl, Int64.add_assoc, ← Int64.ofNat_add, toNat_add, Nat.mul_add]
  have hp0 : (lab l + Int64.ofNat (4 * k)).toBitVec.toNat = (a + 4 * k) % 2 ^ 64 := by
    rw [hlab l a hl, toNat_add]
  unfold blkOkN at h
  unfold blkPh
  rw [List.all_eq_true] at h ⊢
  intro j hj
  have hj' := List.mem_range.mp hj
  have := h j hj
  rw [List.getElem?_eq_getElem hj'] at this ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at this ⊢
  obtain ⟨⟨o1, o2⟩, o3⟩ := this
  refine ⟨⟨by rw [hpc]; exact o1, by rw [hpc, hp0]; exact o2⟩, ?_⟩
  cases hc : Flow.classify b[j] with
  | none => rw [hc] at o3; cases o3
  | some ai =>
    rw [hc] at o3
    simp only at o3 ⊢
    have hfall : (lab l + Int64.ofNat (4 * k) + Int64.ofNat (4 * j) + Int64.ofNat 4).toBitVec.toNat =
        (a + 4 * (k + j) + 4) % 2 ^ 64 := by
      rw [hlab l a hl, Int64.add_assoc, Int64.add_assoc, ← Int64.ofNat_add, ← Int64.ofNat_add, toNat_add,
        Nat.mul_add]
      congr 1
    cases ht : tgtsN code ((a + 4 * (k + j) + 4) % 2 ^ 64) ra ai with
    | none => rw [ht] at o3; cases o3
    | some ts =>
      rw [ht] at o3
      rw [← hfall] at ht
      have hsub := aiTgts_sub hlab hra ht
      rw [List.all_eq_true] at o3 ⊢
      intro t htm
      have := o3 _ (hsub t htm)
      simp only [Bool.or_eq_true, beq_iff_eq] at this ⊢
      rw [hp0]
      rcases this with e | e
      · exact Or.inl e
      · exact Or.inr (hd _ e)

/-- **A checked single step** at `lab l + 4 k`, its next pc 4 bytes on. -/
theorem step_of_factOk (hlab : ∀ l a, code l = some a → lab l = Int64.ofNat a) {okPc : Nat → Bool}
    {ph : Nat → Nat} {l : String} {k : Nat} (h : factOk code okPc ph (.step l k) = true) :
    okPc (lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true ∧
      ph (lab l + Int64.ofNat (4 * k) + Int64.ofNat 4).toBitVec.toNat =
        ph (lab l + Int64.ofNat (4 * k)).toBitVec.toNat := by
  simp only [factOk] at h
  cases hc : code l with
  | none => rw [hc] at h; cases h
  | some a =>
    rw [hc] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [hlab l a hc, toNat_add, Int64.add_assoc, ← Int64.ofNat_add, toNat_add, ← Nat.add_assoc]
    exact h

/-- **A checked pc off the sites** at `lab l + 4 k`. -/
theorem ok_of_factOk (hlab : ∀ l a, code l = some a → lab l = Int64.ofNat a) {okPc : Nat → Bool}
    {ph : Nat → Nat} {l : String} {k : Nat} (h : factOk code okPc ph (.ok l k) = true) :
    okPc (lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true := by
  simp only [factOk] at h
  cases hc : code l with
  | none => rw [hc] at h; cases h
  | some a => rw [hc] at h; rw [hlab l a hc, toNat_add]; exact h

/-- **Two checked distinct pcs.** -/
theorem ne_of_factOk (hlab : ∀ l a, code l = some a → lab l = Int64.ofNat a) {okPc : Nat → Bool}
    {ph : Nat → Nat} {l1 l2 : String} {k1 k2 : Nat} (h : factOk code okPc ph (.ne l1 k1 l2 k2) = true) :
    (lab l1 + Int64.ofNat (4 * k1)).toBitVec.toNat ≠ (lab l2 + Int64.ofNat (4 * k2)).toBitVec.toNat := by
  simp only [factOk] at h
  cases hc1 : code l1 with
  | none => rw [hc1] at h; cases h
  | some a1 =>
    cases hc2 : code l2 with
    | none => rw [hc1, hc2] at h; cases h
    | some a2 =>
      rw [hc1, hc2] at h
      rw [hlab l1 a1 hc1, hlab l2 a2 hc2, toNat_add, toNat_add]
      simpa using h

/-- **A checked phase index** at `lab l + 4 k`. -/
theorem ph_of_factOk (hlab : ∀ l a, code l = some a → lab l = Int64.ofNat a) {okPc : Nat → Bool}
    {ph : Nat → Nat} {l : String} {k v : Nat} (h : factOk code okPc ph (.ph l k v) = true) :
    ph (lab l + Int64.ofNat (4 * k)).toBitVec.toNat = v := by
  simp only [factOk] at h
  cases hc : code l with
  | none => rw [hc] at h; cases h
  | some a => rw [hc] at h; rw [hlab l a hc, toNat_add]; simpa using h

/-- **A checked block fact gives `blkPh`** at `lab l + 4 k`. -/
theorem blkPh_of_factOk (hlab : ∀ l a, code l = some a → lab l = Int64.ofNat a) {okPc : Nat → Bool}
    {ph : Nat → Nat} {l : String} {k : Nat} {b : List Directive} {ra : Option String}
    {dead : Option String} {rapc : Int64} (hra : ∀ r, ra = some r → rapc = lab r)
    {dset : Nat → Bool} (hd : ∀ t, deadN code dead t = true → dset t = true)
    (h : factOk code okPc ph (.blk l k b ra dead) = true) :
    blkPh okPc ph dset lab (lab l + Int64.ofNat (4 * k)) rapc b = true := by
  simp only [factOk] at h
  cases hc : code l with
  | none => rw [hc] at h; cases h
  | some a => rw [hc] at h; exact blkPh_of_blkOkN hlab hc hra hd h

end Spike.Lib.A64.Rt.PhOfTab
