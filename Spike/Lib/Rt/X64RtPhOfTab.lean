/-
**The runtime's phase facts from the decided table** (x86-64; the generic
part of the consumer glue of `Scc/Cert/Rt/RtPhX64.lean`): a fact that
passes `factOk` with the labels resolved by `code` gives the hand proofs'
form at any label map `lab` agreeing with `code` where it resolves
(`hlab`; the loader's, `label_threadAt_of_codeLabel`):

- `blkPh_of_blkOk`: `.blk l o b ra dead` gives `blkPh` at `lab l + o`, a
  `ret` returning to `lab r + o'` (`ra = some (r, o')`), any dead set
  holding the label `dead`'s address;
- `step_of_factOk`, `ok_of_factOk`, `ne_of_factOk`, `ph_of_factOk`: the
  single-pc facts at `lab l + o`.

The per-function projections (`TcbPh`, `TakePh`, `TiPh`, `SwPh`, `MainPh`
from `rtPh_of_placeOK`/`mainPh_of_placeOK`) build on these.
-/
import Scc.Cert.Rt.RtPhX64
import Spike.Lib.X64SegInst

namespace Spike.Lib.X64.Rt.PhOfTab

open Kraken Kraken.Promising Kraken.Promising.X64 Spike.Lib.X64 Spike.Lib.X64Consumer
open Scc.Cert.Rt.X64 (PhFact factOk blkOkN tgtsN deadN pcAt)

variable {code : String → Option Nat} {lab : Label → Int64}

/-- An address `a + o` as a pc: `Int64.ofNat a + Int64.ofNat o` reads
`(a + o) % 2 ^ 64`. -/
theorem toNat_add (a o : Nat) : (Int64.ofNat a + Int64.ofNat o).toBitVec.toNat = (a + o) % 2 ^ 64 := by
  rw [← Int64.ofNat_add]; simp

/-- A resolved label read through `lab`. -/
theorem pcAt_eq (hlab : ∀ l a, code l = some a → lab l = Int64.ofNat a) {l : String} {o t : Nat}
    (h : pcAt code l o = some t) : (lab l + Int64.ofNat o).toBitVec.toNat = t := by
  unfold pcAt at h
  cases hc : code l with
  | none => rw [hc] at h; cases h
  | some a => rw [hc] at h; cases h; rw [hlab l a hc, toNat_add]

/-- A resolved label at offset `0`. -/
theorem pcAt0_eq (hlab : ∀ l a, code l = some a → lab l = Int64.ofNat a) {l : String} {t : Nat}
    (h : pcAt code l 0 = some t) : (lab l).toBitVec.toNat = t := by
  have := pcAt_eq hlab h
  rwa [show Int64.ofNat 0 = 0 from rfl, Int64.add_zero] at this

/-- **An instruction's checked targets are `aiTgts`'** (their pcs), the
return address `lab r + o'`. -/
theorem aiTgts_sub (hlab : ∀ l a, code l = some a → lab l = Int64.ofNat a) {fall : Int64}
    {ra : Option (String × Nat)} {rapc : Int64}
    (hra : ∀ r o', ra = some (r, o') → rapc = lab r + Int64.ofNat o') {ai : AI} {ts : List Nat}
    (h : tgtsN code fall.toBitVec.toNat ra ai = some ts) :
    ∀ t ∈ aiTgts lab fall rapc ai, t.toBitVec.toNat ∈ ts := by
  intro t ht
  cases ai with
  | jmp L | call L =>
    simp only [tgtsN, aiTgts, List.mem_singleton] at h ht
    obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp h
    subst ht; simp [pcAt0_eq hlab ht']
  | jcc cc L =>
    simp only [tgtsN, aiTgts, List.mem_cons, List.not_mem_nil, or_false] at h ht
    obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp h
    rcases ht with rfl | rfl
    · simp [pcAt0_eq hlab ht']
    · simp
  | ret =>
    simp only [tgtsN, aiTgts, List.mem_singleton] at h ht
    cases hr : ra with
    | none => rw [hr] at h; cases h
    | some p =>
      obtain ⟨r, o'⟩ := p
      rw [hr] at h
      obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp h
      subst ht; rw [hra r o' hr, pcAt_eq hlab ht']; simp
  | _ =>
    simp only [tgtsN, aiTgts, List.mem_singleton, Option.some.injEq] at h ht
    subst ht; subst h; simp

/-- **A checked block passes `blkPh`** at `lab l + o` (`a` the label's
address), a `ret` returning to `rapc` (`lab r + o'` for `ra = some (r, o')`),
any dead set holding the label `dead`'s address. -/
theorem blkPh_of_blkOkN (hlab : ∀ l a, code l = some a → lab l = Int64.ofNat a) {okPc : Nat → Bool}
    {ph : Nat → Nat} {l : String} {a o : Nat} (hl : code l = some a) {b : List (Directive × Nat)}
    {ra : Option (String × Nat)} {dead : Option String} {rapc : Int64}
    (hra : ∀ r o', ra = some (r, o') → rapc = lab r + Int64.ofNat o') {dset : Nat → Bool}
    (hd : ∀ t, deadN code dead t = true → dset t = true)
    (h : blkOkN code okPc ph a o b ra dead = true) :
    blkPh okPc ph dset lab (lab l + Int64.ofNat o) rapc b = true := by
  have hpc : ∀ j, (lab l + Int64.ofNat o + Int64.ofNat j).toBitVec.toNat = (a + o + j) % 2 ^ 64 := by
    intro j; rw [hlab l a hl, Int64.add_assoc, ← Int64.ofNat_add, toNat_add, Nat.add_assoc]
  have hp0 : (lab l + Int64.ofNat o).toBitVec.toNat = (a + o) % 2 ^ 64 := by
    rw [hlab l a hl, toNat_add]
  unfold blkOkN at h
  unfold blkPh
  rw [List.all_eq_true] at h ⊢
  intro k hk
  have hk' := List.mem_range.mp hk
  have := h k hk
  rw [List.getElem?_eq_getElem hk'] at this ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at this ⊢
  obtain ⟨⟨o1, o2⟩, o3⟩ := this
  refine ⟨⟨by rw [hpc]; exact o1, by rw [hpc, hp0]; exact o2⟩, ?_⟩
  cases hc : classify b[k].1 with
  | none => rw [hc] at o3; cases o3
  | some ai =>
    rw [hc] at o3
    simp only at o3 ⊢
    have hfall : (lab l + Int64.ofNat o + Int64.ofNat (cellOff b k) + Int64.ofNat b[k].2).toBitVec.toNat =
        (a + o + cellOff b k + b[k].2) % 2 ^ 64 := by
      rw [Int64.add_assoc (lab l + Int64.ofNat o), ← Int64.ofNat_add, hpc, Nat.add_assoc (a + o)]
    cases ht : tgtsN code ((a + o + cellOff b k + b[k].2) % 2 ^ 64) ra ai with
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

/-- **A checked single step** at `lab l + o`, its next pc `z` bytes on. -/
theorem step_of_factOk (hlab : ∀ l a, code l = some a → lab l = Int64.ofNat a) {okPc : Nat → Bool}
    {ph : Nat → Nat} {l : String} {o z : Nat} (h : factOk code okPc ph (.step l o z) = true) :
    okPc (lab l + Int64.ofNat o).toBitVec.toNat = true ∧
      ph (lab l + Int64.ofNat o + Int64.ofNat z).toBitVec.toNat = ph (lab l + Int64.ofNat o).toBitVec.toNat := by
  simp only [factOk] at h
  cases hc : code l with
  | none => rw [hc] at h; cases h
  | some a =>
    rw [hc] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [hlab l a hc, toNat_add, Int64.add_assoc, ← Int64.ofNat_add, toNat_add, ← Nat.add_assoc]
    exact h

/-- **A checked pc off the sites** at `lab l + o`. -/
theorem ok_of_factOk (hlab : ∀ l a, code l = some a → lab l = Int64.ofNat a) {okPc : Nat → Bool}
    {ph : Nat → Nat} {l : String} {o : Nat} (h : factOk code okPc ph (.ok l o) = true) :
    okPc (lab l + Int64.ofNat o).toBitVec.toNat = true := by
  simp only [factOk] at h
  cases hc : code l with
  | none => rw [hc] at h; cases h
  | some a => rw [hc] at h; rw [hlab l a hc, toNat_add]; exact h

/-- **Two checked distinct pcs.** -/
theorem ne_of_factOk (hlab : ∀ l a, code l = some a → lab l = Int64.ofNat a) {okPc : Nat → Bool}
    {ph : Nat → Nat} {l1 l2 : String} {o1 o2 : Nat} (h : factOk code okPc ph (.ne l1 o1 l2 o2) = true) :
    (lab l1 + Int64.ofNat o1).toBitVec.toNat ≠ (lab l2 + Int64.ofNat o2).toBitVec.toNat := by
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

/-- **A checked phase index** at `lab l + o`. -/
theorem ph_of_factOk (hlab : ∀ l a, code l = some a → lab l = Int64.ofNat a) {okPc : Nat → Bool}
    {ph : Nat → Nat} {l : String} {o v : Nat} (h : factOk code okPc ph (.ph l o v) = true) :
    ph (lab l + Int64.ofNat o).toBitVec.toNat = v := by
  simp only [factOk] at h
  cases hc : code l with
  | none => rw [hc] at h; cases h
  | some a => rw [hc] at h; rw [hlab l a hc, toNat_add]; simpa using h

/-- **A checked block fact gives `blkPh`** at `lab l + o`. -/
theorem blkPh_of_factOk (hlab : ∀ l a, code l = some a → lab l = Int64.ofNat a) {okPc : Nat → Bool}
    {ph : Nat → Nat} {l : String} {o : Nat} {b : List (Directive × Nat)} {ra : Option (String × Nat)}
    {dead : Option String} {rapc : Int64} (hra : ∀ r o', ra = some (r, o') → rapc = lab r + Int64.ofNat o')
    {dset : Nat → Bool} (hd : ∀ t, deadN code dead t = true → dset t = true)
    (h : factOk code okPc ph (.blk l o b ra dead) = true) :
    blkPh okPc ph dset lab (lab l + Int64.ofNat o) rapc b = true := by
  simp only [factOk] at h
  cases hc : code l with
  | none => rw [hc] at h; cases h
  | some a => rw [hc] at h; exact blkPh_of_blkOkN hlab hc hra hd h

end Spike.Lib.X64.Rt.PhOfTab
