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

/-- **A grow stub's call to `scc_rt_morestack`** (the caller's `hms`): from
the call node `nC g` (the return address `ra'` at offset `kc`, `%rbp` the
region's base, the frame record `(a g, b g)` in its cells) to the landing
node `nX g'` at the return address, at the ghost `g'` the moved frame
belongs to, given the trampoline's code and its calls to `scc_rt_grow` and
`scc_rt_stack_release` (`hgrow`, `hrel`; see the module docstring). -/
theorem seg_ms_call {γ : Sort _} {Rg : γ → Region} {Fg : γ → MachineData → Prop} {a b : γ → BitVec 64}
    {nC nX : γ → ND} {kc : Int} {ra' : BitVec 64} (hcode : Code exe endPc)
    (hR : ∀ g, (Rg g).OK) (hFg : ∀ g, FStable (Rg g) (Fg g))
    (hlo : ∀ g, (Rg g).lo ≤ kc - 16) (hhi : ∀ g, 16 ≤ (Rg g).hi)
    (hkc : kc + 8 ≤ 0) (hk8 : kc % 8 = 0)
    (hC : ∀ g, (nC g).pc = (_root_.Executable.labels exe).label "scc_rt_morestack" ∧
      (nC g).o = ⟨kc, [(.rbp, 0)]⟩)
    (hJC : ∀ g σ c, (nC g).J σ c → c = c0 ∧ σ.slot 0 = a g ∧ σ.slot 8 = b g ∧ σ.slot kc = ra')
    (hX : ∀ g, (nX g).pc = Int64.ofBitVec ra' ∧ (nX g).o = ⟨kc + 8, [(.rbp, 0)]⟩)
    (hJX : ∀ g σ, σ.slot 0 = a g → σ.slot 8 = b g → (nX g).J σ c0)
    (hgrow : ∀ g need, Seg p lbl ms
      (At exe endPc (msR (Rg g) kc) (Fms (Fg g) (Rg g) kc (a g) (b g))
        (nGrow (_root_.Executable.labels exe).label (msR (Rg g) kc) c0 ra' need ((Rg g).addr 0)))
      (fun s c => ∃ v ob osz, At exe endPc (msR (Rg g) kc)
        (Moved (msR (Rg g) kc) ra' ((Rg g).addr 0) (F'ms Rg Fg a b (msR (Rg g) kc) kc) v)
        (nG1 (_root_.Executable.labels exe).label (msR (Rg g) kc) c0 v ob osz) s c))
    (hrel : ∀ g v ob osz, Seg p lbl ms
      (At exe endPc (rN v) (F'ms Rg Fg a b (msR (Rg g) kc) kc v)
        (nRel (_root_.Executable.labels exe).label c0 ra' ((Rg g).addr 0 + (v - (msR (Rg g) kc).addr 0)) ob osz))
      (At exe endPc (rN v) (F'ms Rg Fg a b (msR (Rg g) kc) kc v)
        (nR1 (_root_.Executable.labels exe).label c0 ra' ((Rg g).addr 0 + (v - (msR (Rg g) kc).addr 0)))))
    (g : γ) :
    Seg p lbl ms (At exe endPc (Rg g) (Fg g) (nC g))
      (fun s c => ∃ g', At exe endPc (Rg g') (Fg g') (nX g') s c) := by
  have hRg := hR g
  have hlog := hlo g
  have hhig := hhi g
  let R' := msR (Rg g) kc
  have hR' : R'.OK := Region.callee_ok hRg (by omega) (by omega) (by omega) (by omega)
  -- the trampoline's frame conditions
  have hF : FStable R' (Fms (Fg g) (Rg g) kc (a g) (b g)) := fun m m' hm hd =>
    ⟨FStable.callee hRg (by omega) (by omega) (by omega) (by omega) (hFg g) m m' hm.1 hd,
      Frame.stable hRg (by omega) (by omega) (by omega) (by omega) rfl rfl (by omega) (by omega) hhig m m'
        hm.2 hd⟩
  have hF'R : ∀ v, FStable R' (F'ms Rg Fg a b R' kc v) := by
    rintro v m m' ⟨g', hv, hd, hst, hFm, hfr⟩ hD
    exact ⟨g', hv, hd, hst, hst m m' hFm hD,
      Frame.stable_out (hR g') hd (by have := hlo g'; omega) (hhi g') m m' hfr hD⟩
  have hF'' : ∀ v, FStable (rN v) (F'ms Rg Fg a b R' kc v) := by
    rintro v m m' ⟨g', hv, hd, hst, hFm, hfr⟩ hD
    have hlo' := hlo g'
    have hhi' := hhi g'
    have hsw : rN v = (Rg g').callee (kc - 8) (-8) 16 := by rw [Region.callee, hv]; rfl
    rw [hsw] at hD
    exact ⟨g', hv, hd, hst,
      FStable.callee (hR g') (by omega) (by omega) (by omega) (by omega) (hFg g') m m' hFm hD,
      Frame.stable (hR g') (by omega) (by omega) (by omega) (by omega) rfl rfl (by omega) (by omega)
        hhi' m m' hfr hD⟩
  -- the call, seen from the trampoline
  refine Seg.mono_pre (P := fun s c => ∃ need : BitVec 64,
      At exe endPc R' (Fms (Fg g) (Rg g) kc (a g) (b g))
        (nE (_root_.Executable.labels exe).label R' c0 ra' need ((Rg g).addr 0)) s c)
    (Seg.exists_pre fun need => ?_) ?_
  · refine (seg_morestack hcode hF hF'R hF'' hR' (Int.le_refl _) (Int.le_refl _) (hgrow g need)
      (hrel g)).mono_post ?_
    -- the return, seen from the caller at the moved frame
    rintro s c ⟨v, he, hn, hdc, hpc, σx, hAx, ⟨g', hv, -, -, hFm, hc, ⟨j1, hj1, hv1⟩, ⟨j2, hj2, hv2⟩⟩, hc0, hbp⟩
    have hsw : (Rg g').callee (kc - 8) (-8) 16 = rN v := by rw [Region.callee, hv]; rfl
    refine ⟨g', he, hn, hdc, by rw [hpc, (hX g').1]; rfl, landed (Rg g') (kc - 8) s.st.1 σx, ?_, hFm, ?_⟩
    · rw [(hX g').2]
      refine ⟨hAx.regs, hAx.zmms, hAx.status, ?_, fun k hk => ?_⟩
      · intro r k' hr
        rcases SO.get_sp_bp hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have := hAx.so .rsp 16 (by simp [nRet, SO.get])
          simp only [landed] at this ⊢
          rw [this, ← hv]
          simp only [rN, swR, Region.addr]
          rw [BitVec.add_assoc, ← BitVec.ofInt_add]
          congr 2; omega
        · simp only [landed]
          rw [hbp, ← hv]
          unfold R'
          simp only [msR, Region.callee, Region.addr]
          bv_omega
      · by_cases hin : ((Rg g').callee (kc - 8) (-8) 16).Off (k - (kc - 8))
        · rw [hsw] at hin
          obtain ⟨j, hj, hjv⟩ := hAx.slot _ hin
          refine ⟨j, ?_, ?_⟩
          · rw [← hsw, Region.callee_addr, show kc - 8 + (k - (kc - 8)) = k by omega] at hj; exact hj
          · simp only [landed]; rw [hsw, ite_eq_left hin]; exact hjv
        · obtain ⟨j, hj⟩ := hc k hk hin
          refine ⟨j, hj, ?_⟩
          simp only [landed]; rw [ite_eq_right hin, hj]; rfl
    · subst hc0
      have n0 : ¬ ((Rg g').callee (kc - 8) (-8) 16).Off (0 - (kc - 8)) := fun h => by
        obtain ⟨-, -, h3⟩ := h; simp only [Region.callee] at h3; omega
      have n8 : ¬ ((Rg g').callee (kc - 8) (-8) 16).Off (8 - (kc - 8)) := fun h => by
        obtain ⟨-, -, h3⟩ := h; simp only [Region.callee] at h3; omega
      refine hJX g' _ ?_ ?_
      · simp only [landed]; rw [ite_eq_right n0, hj1]; exact hv1
      · simp only [landed]; rw [ite_eq_right n8, hj2]; exact hv2
  · -- the caller's state at the call, seen from the trampoline
    rintro s c ⟨he, hn, hdc, hpc, σC, hA, hD, hJ⟩
    obtain ⟨hc, h0, h8, hra⟩ := hJC g σC c hJ
    rw [(hC g).2] at hA
    have hsp := hA.so .rsp kc (by simp [SO.get])
    have hbp := hA.so .rbp 0 (by simp [SO.get, lk])
    refine ⟨σC.regs.get64 .rdi, he, hn, hdc, by rw [hpc, (hC g).1]; rfl, enter (kc - 8) σC, ?_, ⟨hD, ?_, ?_, ?_⟩, ?_⟩
    · refine ⟨hA.regs, hA.zmms, hA.status, ?_, fun k hk => ?_⟩
      · intro r k' hr
        obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
        simp only [enter]
        rw [hsp, Region.callee_addr]; congr 1; omega
      · obtain ⟨j, hj, hjv⟩ := hA.slot _ (Region.callee_off (by omega) (by omega) (by omega) hk)
        exact ⟨j, by rw [Region.callee_addr]; exact hj, hjv⟩
    · intro k hk _
      obtain ⟨j, hj, -⟩ := hA.slot k hk
      exact ⟨j, hj⟩
    · obtain ⟨j, hj, hjv⟩ := hA.slot 0 ⟨rfl, by omega, by omega⟩
      exact ⟨j, hj, hjv.trans h0⟩
    · obtain ⟨j, hj, hjv⟩ := hA.slot 8 ⟨rfl, by omega, by omega⟩
      exact ⟨j, hj, hjv.trans h8⟩
    · refine ⟨hc, ?_, ?_, rfl, hbp⟩
      · simp only [enter]
        rw [hsp, Region.callee_addr]; congr 1; omega
      · simp only [enter]
        rw [show kc - 8 + 8 = kc by omega]; exact hra

end Proof

end Scc.Cert.Rt.X64.Morestack
