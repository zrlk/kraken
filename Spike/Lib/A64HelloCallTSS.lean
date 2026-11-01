/-
**A runtime call inside a frame-aware fragment** (row
5j-misc, AArch64): `A64WakeNN.call_ndTS` (a `bl` to a runtime function, no
source call, the caller's control kept) over `Spike/Lib/HelloSegTCS.lean`'s
`SegTCS` at fixed frames `fs`, so the thread worker's call of `wc_worker`
(whose `print` call pushes a source frame) is one `SegTCS` segment.

- `call_ndTSS`: the call node, a `SegTCS` segment at `fs` to the caller's
  nodes, given the callee's `SegTCS` segment at `fs` (at `call_ndTS`'s
  regions and frame conditions). The proof is `call_ndTS`'s.
-/
import Spike.Lib.A64HelloCallTCS
import Spike.Lib.A64WakeNN

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.HelloSegTCS (SegTCS)

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A runtime call node inside `S` at frames `fs`** (`call_ndTS` over
`SegTCS`): the callee's specification is a `SegTCS` segment at `fs` from
its entry to its exits; its exits land at the caller's nodes (`hret`). -/
theorem call_ndTSS {S : FragS isaLSE2} {nC : ND} {γ : Type _} {κ' : Sort _} {lo' hi' : Int} {Ne : γ → ND}
    {Ex : γ → κ' → ND} {fs : List TermRun.Frame}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp + lo') (hlo0 : lo' ≤ 0) (hkc : nC.o.sp < R.hi) (hhi0 : hi' ≤ 0)
    (hk16 : nC.o.sp % 16 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ lo' →
      hi' ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ g,
        SegTCS S p lbl ms ((At exe endPc R' F' (Ne g)).at fs)
          (Frag.at (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c) fs))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter nC.o.sp σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter nC.o.sp σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp + (Ex g x).o.sp, []⟩, σR⟩ c') :
    SegTCS S p lbl ms ((At exe endPc R F nC).at fs) ((Next exe endPc R F N E).at fs) := by
  -- the callee's region and its ghost-indexed frame condition
  let kc := nC.o.sp
  let R' := R.callee kc lo' hi'
  have hR' : R'.OK := Region.callee_ok hR hlo hlo0 hkc (by omega)
  have hb' := Region.callee_base (hi' := hi') hR hlo hlo0 hkc
  have hal' : R'.base.toNat % 16 = 0 := by
    have : ((R'.base.toNat : Int)) % 16 = 0 := by rw [hb']; omega
    omega
  have hFR' : FStable R' F := FStable.callee hR hlo hlo0 hkc (by omega) hF
  -- the ghost: the machine data and abstract state at the call, the caller's control, the callee's
  -- parameters; the facts about it ride in the frame condition (constant, so stable)
  let F' : MachineData × AS × Ctl × γ → MachineData → Prop := fun G m =>
    F m ∧ DFrame R' G.1 m ∧ Abs R nC.o G.1 G.2.1 ∧ nC.J G.2.1 G.2.2.1 ∧ (Ne G.2.2.2).J (enter kc G.2.1) G.2.2.1
  have hF' : ∀ G, FStable R' (F' G) := fun G m m' hm hd =>
    ⟨hFR' m m' hm.1 hd, hm.2.1.trans hd, hm.2.2⟩
  refine SegTCS.mono_pre (P := fun s c fs' => ∃ G, (At exe endPc R' (F' G) (Ne G.2.2.2)).at fs s c fs')
    (SegTCS.exists_pre fun G => ?_) ?_
  · -- the callee's segment, its exits landing at the caller's nodes
    refine (hcallee R' (F' G) hR' hal' (Int.le_refl _) (Int.le_refl _) (hF' G) (fun _ h => h.1)
      G.2.2.2).mono_post ?_
    rintro s c fs' ⟨⟨x, he, hn, hdc, hpc, σx, hAx, ⟨hD, hDF, hAC, hJC, hJE⟩, hJx⟩, rfl⟩
    refine ⟨?_, rfl⟩
    obtain ⟨mC, σC, cC, g⟩ := G
    simp only at hDF hAC hJC hJE hJx hAx hpc
    have hAR : Abs R ⟨kc + (Ex g x).o.sp, []⟩ s.st.1 (leave R' kc σC σx) := by
      refine ⟨hAx.regs, hAx.status, ?_, fun k hk => ?_⟩
      · intro r k' hr
        rcases r with y | _
        · cases hr
        · simp only [SO.get, Option.some.injEq] at hr
          subst hr
          have := hAx.so .SP _ rfl
          simp only [leave] at this ⊢
          rw [this, Region.callee_addr]
      · by_cases hin : R'.Off (k - kc)
        · obtain ⟨j, hj, hv⟩ := hAx.slot _ hin
          refine ⟨j, ?_, ?_⟩
          · rw [Region.callee_addr, show kc + (k - kc) = k by omega] at hj; exact hj
          · simp only [leave]; rw [ite_eq_left hin]; exact hv
        · obtain ⟨j, hj, hv⟩ := hAC.slot k hk
          refine ⟨j, ?_, ?_⟩
          · rw [hDF _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkc (by omega) hl8 hh8 hk hin)]
            exact hj
          · simp only [leave]; rw [ite_eq_right hin]; exact hv
    have hL := hret g x σC cC σx c (leave R' kc σC σx) hJC hJE hJx rfl rfl
      (fun k _ hn => by simp only [leave]; exact ite_eq_right hn)
    have hs : s = { s with st := (s.st.1, (Ex g x).pc) } := by rw [← hpc]; rfl
    rw [hs]
    rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
    · exact .inl ⟨j, hj.at he hn hdc hAR hD⟩
    · exact .inr ⟨y, hy.at he hn hdc hAR hD⟩
  · -- the caller's state at the call, seen from the callee
    rintro s c fs' ⟨⟨he, hn, hdc, hpc, σC, hA, hD, hJ⟩, rfl⟩
    obtain ⟨g, hgpc, hgJ⟩ := hent σC c hJ
    refine ⟨(s.st.1, σC, c, g), ⟨he, hn, hdc, by rw [hpc, hgpc], enter kc σC, ?_,
      ⟨hD, DFrame.refl _ _, hA, hJ, hgJ⟩, hgJ⟩, rfl⟩
    rw [hNe]
    refine ⟨hA.regs, hA.status, ?_, fun k hk => ?_⟩
    · intro r k' hr
      rcases r with y | _
      · cases hr
      · simp only [SO.get, Option.some.injEq] at hr
        subst hr
        have := hA.so .SP _ rfl
        simp only [enter] at this ⊢
        rw [this, Region.callee_addr, Int.add_zero]
    · obtain ⟨j, hj, hv⟩ := hA.slot _ (Region.callee_off hlo (by omega) (by omega) hk)
      exact ⟨j, by rw [Region.callee_addr]; exact hj, hv⟩

end Fn

end Spike.Lib.A64.Flow

/-- info: 'Spike.Lib.A64.Flow.call_ndTSS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.call_ndTSS
