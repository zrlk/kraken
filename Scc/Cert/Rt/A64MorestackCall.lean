import Scc.Cert.Rt.A64Morestack
import Spike.Lib.A64Call

/-!
# A grow stub's call to `scc_rt_morestack` on AArch64

A compiled function's stack grow path (`Scc.Emit.A64`, the grow stub) saves
its argument registers and its frame record (`x29`, `x30` at offsets `-16`
and `-8` of its region) below the stack pointer, and calls
`scc_rt_morestack` with `sp` at offset `kc` of its region. The trampoline
copies the stack to a new range and returns there: the caller's frame has
moved. `seg_ms_call` is the caller's given node for that call
(`Spike/Lib/A64PrintL.lean`'s `hms`): from the call node `nC g`, in the
caller's region `Rg g` with frame condition `Fg g`, to the landing node
`nX g'` at some ghost `g'` (`fn_seg_g`), by `seg_morestack`.

At the call, the trampoline runs in the caller's region at offset `kc`
(`msR`, cells `[kc - 16, kc)`, its frame record), with the frame condition
`Fms`: the caller's, and the caller's cells outside the trampoline's mapped
with the frame record `(a g, b g)` at `-16`, `-8` (`Frame`). After
`scc_rt_grow`, the moved frame satisfies `F'ms`: some ghost `g'` whose
region holds the trampoline's new region `swR v 0 16` at offset `kc - 16`,
with `g'`'s frame condition, disjoint from the trampoline's old region (and
`g'`'s frame condition not broken by writes there), and the caller's cells
outside the trampoline's mapped with `g'`'s frame record. These are what the
calls to `scc_rt_grow` and `scc_rt_stack_release` (`hgrow`, `hrel`, given
nodes) must establish and keep.

The theorems stated over the segment predicate (`Spike.Lib.Seg`, `MemSide`)
are in `Spike/Lib/Rt/Seg/A64MorestackCall.lean` (same namespace and names).
-/

namespace Scc.Cert.Rt.A64.Morestack

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib Spike.Lib.A64 Spike.Lib.A64.Flow

/-! ## The caller's frame around the trampoline's -/

/-- The trampoline's region in the caller's region `Rc`, at the caller's
offset `kc` (its frame record below). -/
abbrev msR (Rc : Region) (kc : Int) : Region := Rc.callee kc (-16) 0

/-- **The caller's frame outside a callee's** `Rc.callee kb lo' hi'`: its
cells there mapped, its frame record `(a, b)` at offsets `-16` and `-8`. -/
def Frame (Rc : Region) (kb lo' hi' : Int) (a b : BitVec 64) (m : MachineData) : Prop :=
  (∀ k, Rc.Off k → ¬ (Rc.callee kb lo' hi').Off (k - kb) → ∃ j, Mem.loadInt m.dmem (Rc.addr k) 8 = some j) ∧
  (∃ j, Mem.loadInt m.dmem (Rc.addr (-16)) 8 = some j ∧ BitVec.ofInt 64 j = a) ∧
  (∃ j, Mem.loadInt m.dmem (Rc.addr (-8)) 8 = some j ∧ BitVec.ofInt 64 j = b)

/-- Two regions apart. -/
def Disj (R R' : Region) : Prop :=
  (R.base.toNat : Int) + R.hi ≤ R'.base.toNat + R'.lo ∨ (R'.base.toNat : Int) + R'.hi ≤ R.base.toNat + R.lo

/-- The trampoline's frame condition at the call. -/
def Fms (Fc : MachineData → Prop) (Rc : Region) (kc : Int) (a b : BitVec 64) (m : MachineData) : Prop :=
  Fc m ∧ Frame Rc kc (-16) 0 a b m

/-- **The trampoline's frame condition after `scc_rt_grow`**, for its new
frame record `v`: a ghost `g'` whose region holds `swR v 0 16` at offset
`kc - 16`, apart from the trampoline's old region `R'` (and `g'`'s frame
condition not broken by writes there), with `g'`'s frame condition and the
caller's frame around the trampoline's. -/
def F'ms {γ : Sort _} (Rg : γ → Region) (Fg : γ → MachineData → Prop) (a b : γ → BitVec 64) (R' : Region)
    (kc : Int) (v : BitVec 64) (m : MachineData) : Prop :=
  ∃ g', (Rg g').addr (kc - 16) = v ∧ Disj (Rg g') R' ∧ FStable R' (Fg g') ∧ Fg g' m ∧
    Frame (Rg g') (kc - 16) 0 16 (a g') (b g') m

section Stable

variable {Rc : Region} {kb lo' hi' : Int} {a b : BitVec 64}

/-- `Frame` survives writes inside the callee's region. -/
theorem Frame.stable (hR : Rc.OK) (hlo : Rc.lo ≤ kb + lo') (hlo0 : lo' ≤ 0) (hkc : kb < Rc.hi)
    (hk8 : kb % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0) (hwin : kb + hi' ≤ -16) (hfr : -16 ≥ Rc.lo)
    (hfr' : 0 ≤ Rc.hi) :
    FStable (Rc.callee kb lo' hi') (Frame Rc kb lo' hi' a b) := by
  rintro m m' ⟨hc, ⟨j1, hj1, hv1⟩, ⟨j2, hj2, hv2⟩⟩ hD
  have keep : ∀ k, Rc.Off k → ¬ (Rc.callee kb lo' hi').Off (k - kb) →
      Mem.loadInt m'.dmem (Rc.addr k) 8 = Mem.loadInt m.dmem (Rc.addr k) 8 := fun k hk hn =>
    hD _ (Rc.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkc hk8 hl8 hh8 hk hn)
  have o16 : Rc.Off (-16) := ⟨rfl, hfr, by omega⟩
  have o8 : Rc.Off (-8) := ⟨rfl, by omega, by omega⟩
  have n16 : ¬ (Rc.callee kb lo' hi').Off (-16 - kb) := fun h => by
    obtain ⟨-, -, h3⟩ := h; simp only [Region.callee] at h3; omega
  have n8 : ¬ (Rc.callee kb lo' hi').Off (-8 - kb) := fun h => by
    obtain ⟨-, -, h3⟩ := h; simp only [Region.callee] at h3; omega
  refine ⟨fun k hk hn => (keep k hk hn).symm ▸ hc k hk hn, ⟨j1, (keep _ o16 n16).trans hj1, hv1⟩,
    ⟨j2, (keep _ o8 n8).trans hj2, hv2⟩⟩

/-- `Frame` survives writes inside a region apart from the caller's. -/
theorem Frame.stable_out {R'' : Region} (hR : Rc.OK) (hd : Disj Rc R'') (hfr : -16 ≥ Rc.lo)
    (hfr' : 0 ≤ Rc.hi) : FStable R'' (Frame Rc kb lo' hi' a b) := by
  rintro m m' ⟨hc, ⟨j1, hj1, hv1⟩, ⟨j2, hj2, hv2⟩⟩ hD
  have keep : ∀ k, Rc.Off k → Mem.loadInt m'.dmem (Rc.addr k) 8 = Mem.loadInt m.dmem (Rc.addr k) 8 :=
    fun k hk => hD _ (Rc.addr_fit hR hk) (by
      have ha := Region.addr_toNat hR hk
      obtain ⟨-, h2, h3⟩ := hk
      unfold Disj at hd; omega)
  have o16 : Rc.Off (-16) := ⟨rfl, hfr, by omega⟩
  have o8 : Rc.Off (-8) := ⟨rfl, by omega, by omega⟩
  exact ⟨fun k hk hn => (keep k hk).symm ▸ hc k hk hn, ⟨j1, (keep _ o16).trans hj1, hv1⟩,
    ⟨j2, (keep _ o8).trans hj2, hv2⟩⟩

end Stable

/-! ## The call -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {c0 : Ctl}

open Classical in
/-- The caller's abstract state after the trampoline's return: the
trampoline's registers and flags, its cells inside its new region (at the
caller's offset `kb`), the memory's outside. -/
noncomputable def landed (Rc : Region) (kb : Int) (m : MachineData) (σx : Flow.AS) : Flow.AS :=
  { regs := σx.regs, status := σx.status,
    slot := fun k => if (Rc.callee kb 0 16).Off (k - kb) then σx.slot (k - kb)
      else BitVec.ofInt 64 ((Mem.loadInt m.dmem (Rc.addr k) 8).getD 0) }

end Proof

end Scc.Cert.Rt.A64.Morestack
