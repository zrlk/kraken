/-
**A phase extension** (AArch64): the runtime's phase index (`phOf`, four
bits, below 16) with a fifth bit (16) set on a set of pcs `inR`:
`phExt ph inR pc = ph pc + 16 · [inR pc]`.

Wake-specific phase extension; generic multi-spawn needs a reserve phase
bit in PhasesA64 (trusted). The extension lets the thread counter
`scc_rt_nthreads` be owned across `scc_rt_thread_reserve`'s add (the
canonical phases do not tell the pcs before and after it apart).

- `PhTab.ph_lt`, `phOf_lt`: the canonical phase index is below 16.
- `phExt`, `phExt_lo`, `phExt_hi`, `phExt_eq_iff`: the extension; two pcs
  have equal extended phases iff equal phases and the same bit.
- `blkPh_ext`: a block check at `ph` transfers to `phExt ph inR` when every
  pc the check reads has the entry's bit.
-/
import Spike.Lib.A64SegInst
import Scc.Cert.Rt.PhasesA64

namespace Spike.Lib.A64.PhExt

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64Consumer

/-- **The canonical phase index is below 16** (four bits). -/
theorem PhTab_ph_lt (T : Scc.Cert.Rt.A64.PhTab) (pc : Nat) : T.ph pc < 16 := by
  unfold Scc.Cert.Rt.A64.PhTab.ph
  cases Scc.Cert.Rt.A64.inRs T.p pc <;> cases Scc.Cert.Rt.A64.inRs T.l pc <;>
    cases Scc.Cert.Rt.A64.inRs T.n pc <;> cases Scc.Cert.Rt.A64.inRs T.t pc <;> decide

theorem phOf_lt (lo : Nat) (prog : List Directive) (pc : Nat) : Scc.Cert.Rt.A64.phOf lo prog pc < 16 := by
  unfold Scc.Cert.Rt.A64.phOf
  cases Scc.Cert.Rt.A64.phTabOf lo prog with
  | some T => exact PhTab_ph_lt T pc
  | none => exact (by decide : (0 : Nat) < 16)

/-- **The extended phase index**: bit 16 set on `inR`. -/
def phExt (ph : Nat → Nat) (inR : Nat → Bool) (pc : Nat) : Nat := ph pc + 16 * (inR pc).toNat

theorem phExt_lo {ph : Nat → Nat} {inR : Nat → Bool} {pc : Nat} (hlt : ph pc < 16) :
    phExt ph inR pc % 16 = ph pc := by
  unfold phExt; omega

theorem phExt_hi {ph : Nat → Nat} {inR : Nat → Bool} {pc : Nat} (hlt : ph pc < 16) :
    phExt ph inR pc / 16 = (inR pc).toNat := by
  unfold phExt; cases inR pc <;> simp <;> omega

/-- Two pcs have equal extended phases iff equal phases and the same bit. -/
theorem phExt_eq_iff {ph : Nat → Nat} {inR : Nat → Bool} {p q : Nat} (hp : ph p < 16) (hq : ph q < 16) :
    phExt ph inR p = phExt ph inR q ↔ ph p = ph q ∧ inR p = inR q := by
  unfold phExt
  cases hP : inR p <;> cases hQ : inR q <;> simp <;> omega

/-- Equal phases and equal bits give equal extended phases. -/
theorem phExt_eq {ph : Nat → Nat} {inR : Nat → Bool} {p q : Nat}
    (h1 : (ph p == ph q) = true) (h2 : ((inR p).toNat == (inR q).toNat) = true) :
    (phExt ph inR p == phExt ph inR q) = true := by
  simp only [beq_iff_eq] at h1 h2 ⊢
  unfold phExt; rw [h1, h2]

/-- **A block check transfers to the extension** when the entry's bit is
every read pc's bit (its pcs and its non-dead targets). -/
theorem blkPh_ext {okPc : Nat → Bool} {ph : Nat → Nat} {inR : Nat → Bool} {dead : Nat → Bool}
    {lab : Label → Int64} {pc ra : Int64} {blk : List Directive}
    (h : blkPh okPc ph dead lab pc ra blk = true)
    (hb : blkPh okPc (fun p => (inR p).toNat) dead lab pc ra blk = true) :
    blkPh okPc (phExt ph inR) dead lab pc ra blk = true := by
  unfold blkPh at h hb ⊢
  rw [List.all_eq_true] at h hb ⊢
  intro k hk
  have h1 := h k hk
  have h2 := hb k hk
  generalize blk[k]? = o at h1 h2 ⊢
  rw [Bool.and_eq_true, Bool.and_eq_true] at h1 h2 ⊢
  obtain ⟨⟨ho, hp⟩, hm⟩ := h1
  obtain ⟨⟨-, hp2⟩, hm2⟩ := h2
  refine ⟨⟨ho, phExt_eq hp hp2⟩, ?_⟩
  cases o with
  | none => exact hm
  | some d =>
    dsimp only at hm hm2 ⊢
    revert hm hm2
    cases Flow.classify d with
    | none => exact fun hm _ => hm
    | some a =>
      intro hm hm2
      dsimp only at hm hm2 ⊢
      rw [List.all_eq_true] at hm hm2 ⊢
      intro t ht
      have e1 := hm t ht
      have e2 := hm2 t ht
      rw [Bool.or_eq_true] at e1 e2 ⊢
      rcases e1 with e1 | e1
      · rcases e2 with e2 | e2
        · exact .inl (phExt_eq e1 e2)
        · exact .inr e2
      · exact .inr e1

end Spike.Lib.A64.PhExt
