import Scc.Cert.Rt.X64Morestack
import Spike.Lib.X64Call

/-!
# A grow stub's call to `scc_rt_morestack` on x64

The x64 twin of `Scc/Cert/Rt/A64MorestackCall.lean`. A compiled function's
stack grow path (`Scc.Emit.X64`) pushes its argument registers below its
frame record (the caller's `%rbp` at offset 0 of its region, its return
address at 8, `%rbp` the region's base) and calls `scc_rt_morestack`, the
return address at offset `kc`. `seg_ms_call` is the caller's given node for
that call (`Spike/Lib/X64PrintL.lean`'s `hms`): from the call node `nC g`,
in the caller's region `Rg g` with frame condition `Fg g`, to the landing
node `nX g'` (`%rsp` at `kc + 8`, `%rbp` the base) at some ghost `g'`
(`fn_seg_g`), by `seg_morestack`.

At the call, the trampoline runs in the caller's region at offset `kc - 8`
(`msR`, cells `[kc - 16, kc + 8)`: its frame record and the return address),
with the frame condition `Fms`: the caller's, and the caller's cells
outside the trampoline's mapped with the frame record `(a g, b g)` at `0`,
`8` (`Frame`). After `scc_rt_grow`, the moved frame satisfies `F'ms`: some
ghost `g'` whose region holds the trampoline's new region `swR v (-8) 16` at
offset `kc - 8`, with `g'`'s frame condition, apart from the trampoline's
old region (and `g'`'s frame condition not broken by writes there), and the
caller's cells outside the trampoline's mapped with `g'`'s frame record.
These are what the calls to `scc_rt_grow` and `scc_rt_stack_release`
(`hgrow`, `hrel`, given nodes) must establish and keep; `scc_rt_grow` also
moves the trampoline's saved `%rbp` with the stack (`Moved`), so the caller's
`%rbp` comes back as its moved region's base.

The theorems stated over the segment predicate (`Spike.Lib.Seg`, `MemSide`)
are in `Spike/Lib/Rt/Seg/X64MorestackCall.lean` (same namespace and names).
-/

namespace Scc.Cert.Rt.X64.Morestack

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Spike.Lib Spike.Lib.X64

/-! ## The caller's frame around the trampoline's -/

/-- The trampoline's region in the caller's region `Rc`, its return address
at the caller's offset `kc`. -/
abbrev msR (Rc : Region) (kc : Int) : Region := Rc.callee (kc - 8) (-8) 16

/-- **The caller's frame outside a callee's** `Rc.callee kb lo' hi'`: its
cells there mapped, its frame record `(a, b)` at offsets `0` and `8`. -/
def Frame (Rc : Region) (kb lo' hi' : Int) (a b : BitVec 64) (m : MachineData) : Prop :=
  (∀ k, Rc.Off k → ¬ (Rc.callee kb lo' hi').Off (k - kb) → ∃ j, Mem.loadInt m.dmem (Rc.addr k) 8 = some j) ∧
  (∃ j, Mem.loadInt m.dmem (Rc.addr 0) 8 = some j ∧ BitVec.ofInt 64 j = a) ∧
  (∃ j, Mem.loadInt m.dmem (Rc.addr 8) 8 = some j ∧ BitVec.ofInt 64 j = b)

/-- Two regions apart. -/
def Disj (R R' : Region) : Prop :=
  (R.base.toNat : Int) + R.hi ≤ R'.base.toNat + R'.lo ∨ (R'.base.toNat : Int) + R'.hi ≤ R.base.toNat + R.lo

/-- The trampoline's frame condition at the call. -/
def Fms (Fc : MachineData → Prop) (Rc : Region) (kc : Int) (a b : BitVec 64) (m : MachineData) : Prop :=
  Fc m ∧ Frame Rc (kc - 8) (-8) 16 a b m

/-- **The trampoline's frame condition after `scc_rt_grow`**, for its new
frame record `v`: a ghost `g'` whose region holds `swR v (-8) 16` at offset
`kc - 8`, apart from the trampoline's old region `R'` (and `g'`'s frame
condition not broken by writes there), with `g'`'s frame condition and the
caller's frame around the trampoline's. -/
def F'ms {γ : Sort _} (Rg : γ → Region) (Fg : γ → MachineData → Prop) (a b : γ → BitVec 64) (R' : Region)
    (kc : Int) (v : BitVec 64) (m : MachineData) : Prop :=
  ∃ g', (Rg g').addr (kc - 8) = v ∧ Disj (Rg g') R' ∧ FStable R' (Fg g') ∧ Fg g' m ∧
    Frame (Rg g') (kc - 8) (-8) 16 (a g') (b g') m

section Stable

variable {Rc : Region} {kb lo' hi' : Int} {a b : BitVec 64}

/-- `Frame` survives writes inside the callee's region. -/
theorem Frame.stable (hR : Rc.OK) (hlo : Rc.lo ≤ kb + lo') (hlo0 : lo' ≤ 0) (hkc : kb < Rc.hi)
    (hk8 : kb % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0) (hwin : kb + hi' ≤ 0) (hfr : 0 ≥ Rc.lo)
    (hfr' : 16 ≤ Rc.hi) :
    FStable (Rc.callee kb lo' hi') (Frame Rc kb lo' hi' a b) := by
  rintro m m' ⟨hc, ⟨j1, hj1, hv1⟩, ⟨j2, hj2, hv2⟩⟩ hD
  have keep : ∀ k, Rc.Off k → ¬ (Rc.callee kb lo' hi').Off (k - kb) →
      Mem.loadInt m'.dmem (Rc.addr k) 8 = Mem.loadInt m.dmem (Rc.addr k) 8 := fun k hk hn =>
    hD _ (Rc.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkc hk8 hl8 hh8 hk hn)
  have o0 : Rc.Off 0 := ⟨rfl, hfr, by omega⟩
  have o8 : Rc.Off 8 := ⟨rfl, by omega, by omega⟩
  have n0 : ¬ (Rc.callee kb lo' hi').Off (0 - kb) := fun h => by
    obtain ⟨-, -, h3⟩ := h; simp only [Region.callee] at h3; omega
  have n8 : ¬ (Rc.callee kb lo' hi').Off (8 - kb) := fun h => by
    obtain ⟨-, -, h3⟩ := h; simp only [Region.callee] at h3; omega
  refine ⟨fun k hk hn => (keep k hk hn).symm ▸ hc k hk hn, ⟨j1, (keep _ o0 n0).trans hj1, hv1⟩,
    ⟨j2, (keep _ o8 n8).trans hj2, hv2⟩⟩

/-- `Frame` survives writes inside a region apart from the caller's. -/
theorem Frame.stable_out {R'' : Region} (hR : Rc.OK) (hd : Disj Rc R'') (hfr : 0 ≥ Rc.lo)
    (hfr' : 16 ≤ Rc.hi) : FStable R'' (Frame Rc kb lo' hi' a b) := by
  rintro m m' ⟨hc, ⟨j1, hj1, hv1⟩, ⟨j2, hj2, hv2⟩⟩ hD
  have keep : ∀ k, Rc.Off k → Mem.loadInt m'.dmem (Rc.addr k) 8 = Mem.loadInt m.dmem (Rc.addr k) 8 :=
    fun k hk => hD _ (Rc.addr_fit hR hk) (by
      have ha := Region.addr_toNat hR hk
      obtain ⟨-, h2, h3⟩ := hk
      unfold Disj at hd; omega)
  have o0 : Rc.Off 0 := ⟨rfl, hfr, by omega⟩
  have o8 : Rc.Off 8 := ⟨rfl, by omega, by omega⟩
  exact ⟨fun k hk hn => (keep k hk).symm ▸ hc k hk hn, ⟨j1, (keep _ o0).trans hj1, hv1⟩,
    ⟨j2, (keep _ o8).trans hj2, hv2⟩⟩

end Stable

/-! ## The call -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {c0 : Ctl}

open Classical in
/-- The caller's abstract state after the trampoline's return: the
trampoline's registers and flags, its cells inside its new region (at the
caller's offset `kb`), the memory's outside. -/
noncomputable def landed (Rc : Region) (kb : Int) (m : MachineData) (σx : AS) : AS :=
  { regs := σx.regs, zmms := σx.zmms, status := σx.status,
    slot := fun k => if (Rc.callee kb (-8) 16).Off (k - kb) then σx.slot (k - kb)
      else BitVec.ofInt 64 ((Mem.loadInt m.dmem (Rc.addr k) 8).getD 0) }

/-- The offsets `⟨e, [(.rbp, 0)]⟩` know `%rsp` at `e` and `%rbp` at 0. -/
theorem SO.get_sp_bp {e : Int} {r : Reg64} {k : Int} (h : SO.get ⟨e, [(.rbp, 0)]⟩ r = some k) :
    (r = .rsp ∧ k = e) ∨ (r = .rbp ∧ k = 0) := by
  unfold SO.get at h
  split at h
  · rename_i hr; cases h; exact .inl ⟨hr, rfl⟩
  · simp only [lk] at h
    split at h
    · rename_i hr; cases h; exact .inr ⟨hr, rfl⟩
    · cases h

end Proof

end Scc.Cert.Rt.X64.Morestack
