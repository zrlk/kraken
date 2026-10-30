import Scc.Cert.Rt.X64MorestackCall
import Spike.Lib.Rt.Seg.X64Morestack

/-!
# The segment theorems of `Scc.Cert.Rt.X64MorestackCall`

The theorems of `Scc/Cert/Rt/X64MorestackCall.lean` whose statements are stated over the
untrusted segment predicate (`Spike.Lib.Seg`, `MemSide`), moved out of the
trusted tree unchanged (same namespace, names and statements; FENCE1
follow-up 2): `seg_ms_call`. The definitions, code
data and decided checks they use stay in `Scc.Cert.Rt.X64MorestackCall`.
-/

namespace Scc.Cert.Rt.X64.Morestack

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Spike.Lib Spike.Lib.X64

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {c0 : Ctl}

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
