/-
**Source calls on AArch64 whose callee may abort**: `call_ndSA`, the
source call node `call_ndS` (`Spike/Lib/A64CallS.lean`) with an abort
postcondition. The callee's specification is a segment at `fr :: fs` from its
entry to its exits or to `Ab` (pairs at any frames, e.g. a stack-depth abort
taken deeper in the callee, whose rows `Ab`'s user closes); the call node's
segment then ends at the caller's nodes or in `Ab`.
-/
import Spike.Lib.A64CallS

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

open Classical in
/-- **A source call node whose callee may abort, its nodes indexed by the
callee's frame** (`call_ndSA` with the callee's entry `Ne g fr` and exits
`Ex g fr x` depending on the frame `fr` the call pushes, e.g. its exits'
frame runs at `fr :: fs`): as `call_ndSA` (`call_ndS` with an
abort postcondition `Ab`): the callee's specification ends either at its
exits at `fr :: fs` or in `Ab` (at any frames: e.g. a stack-depth abort
deep in the callee), and so does the call node's segment. As `call_ndS`: At the caller's frames `fs`, from the call node `nC` (`hent`: its
source control calls, `CallTo`, and the callee's entry node holds at the
callee's control) to the caller's nodes, the return taken (`hret`: the
source runs from the callee's exit control at `fr :: fs` back to the
caller's frames). The callee's specification (`hcallee`) is a segment at
the frames `fr :: fs`, with `call_nd_FWK`'s regions and frame conditions.
`hWC`: `W` holds at the call node's pairs. -/
theorem call_ndSF {KC : Prop} {W : FragS isaLSE2} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {nC : ND} {γ : Type _} {κ' : Sort _} {lo' hi' : Int} {Ne : γ → TermRun.Frame → ND} {Ex : γ → TermRun.Frame → κ' → ND}
    {fs : List TermRun.Frame} {Ab : FragS isaLSE2}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp + lo') (hlo0 : lo' ≤ 0) (hkc : nC.o.sp < R.hi) (hhi0 : hi' ≤ 0)
    (hk16 : nC.o.sp % 16 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hFK : KC → KStable K F)
    (hKR : KC → ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hF₂ : ∀ m, F m → M m → F₂ m)
    (hWC : ∀ s c, At exe endPc R F nC s c → W s c fs)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ lo' →
      hi' ≤ R'.hi → FStable R' F' → (KC → KStable K F') → (∀ m, F' m → F m) → R' = R.callee nC.o.sp lo' hi' →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - nC.o.sp) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g (fr : TermRun.Frame),
        (∃ σC c cE, nC.J σC c ∧ CallTo p c cE fr ∧ (Ne g fr).J (enter nC.o.sp σC) cE) →
        (∀ m, F' m → ∃ mC σC c cE, Abs R nC.o mC σC ∧ nC.J σC c ∧ CallTo p c cE fr ∧
          (Ne g fr).J (enter nC.o.sp σC) cE ∧
          ∀ k, R.Off k → ¬ R'.Off (k - nC.o.sp) → Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegWS W K p lbl ms ((At exe endPc R' F' (Ne g fr)).at (fr :: fs))
          (fun s c fs' => Frag.at (fun s c => ∃ x, At exe endPc R' F' (Ex g fr x) s c ∧ M s.st.1) (fr :: fs) s c fs' ∨
            Ab s c fs'))
    (hNe : ∀ g fr, (Ne g fr).o = ⟨0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g cE fr, CallTo p c cE fr ∧ (Ne g fr).pc = nC.pc ∧ (Ne g fr).J (enter nC.o.sp σC) cE)
    (hret : ∀ g x σC c cE fr σx c' (σR : AS), nC.J σC c → CallTo p c cE fr → (Ne g fr).J (enter nC.o.sp σC) cE →
      (Ex g fr x).J σx c' → σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      ∃ c'', FrameRun p (c', fr :: fs) (c'', fs) ∧ Lands N E ⟨(Ex g fr x).pc, ⟨nC.o.sp + (Ex g fr x).o.sp, []⟩, σR⟩ c'') :
    SegWS W K p lbl ms ((At exe endPc R F nC).at fs)
      (fun s c fs' => (Next exe endPc R F₂ N E).at fs s c fs' ∨ Ab s c fs') := by
  let kc := nC.o.sp
  let R' := R.callee kc lo' hi'
  have hR' : R'.OK := Region.callee_ok hR hlo hlo0 hkc (by omega)
  have hb' := Region.callee_base (hi' := hi') hR hlo hlo0 hkc
  have hal' : R'.base.toNat % 16 = 0 := by
    have : ((R'.base.toNat : Int)) % 16 = 0 := by rw [hb']; omega
    omega
  have hFR' : FStable R' F := FStable.callee hR hlo hlo0 hkc (by omega) hF
  -- the caller's cells outside the callee's region, as in `m0`
  let Kept : MachineData → MachineData → Prop := fun m0 m =>
    ∀ k, R.Off k → ¬ R'.Off (k - kc) → Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt m0.dmem (R.addr k) 8
  -- the ghost: the machine data and abstract state at the call, the caller's control, the callee's
  -- control and frame, the callee's parameters
  let F' : MachineData × AS × Ctl × Ctl × TermRun.Frame × γ → MachineData → Prop := fun G m =>
    F m ∧ Kept G.1 m ∧ Abs R nC.o G.1 G.2.1 ∧ nC.J G.2.1 G.2.2.1 ∧ CallTo p G.2.2.1 G.2.2.2.1 G.2.2.2.2.1 ∧
      (Ne G.2.2.2.2.2 G.2.2.2.2.1).J (enter kc G.2.1) G.2.2.2.1
  have hF' : ∀ G, FStable R' (F' G) := fun G m m' hm hd =>
    ⟨hFR' m m' hm.1 hd, fun k hk hn =>
      (hd _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkc (by omega) hl8 hh8 hk hn)).trans
        (hm.2.1 k hk hn), hm.2.2⟩
  have hK' : KC → ∀ G, KStable K (F' G) := fun hc G s s' hk hm =>
    ⟨hFK hc s s' hk hm.1, fun k hk' hn => (hKR hc s s' hk hm.1 k hk' hn).trans (hm.2.1 k hk' hn), hm.2.2⟩
  let PE : FragS isaLSE2 := fun s c fs' =>
    ∃ G : MachineData × AS × Ctl × Ctl × TermRun.Frame × γ,
      (At exe endPc R' (F' G) (Ne G.2.2.2.2.2 G.2.2.2.2.1)).at (G.2.2.2.2.1 :: fs) s c fs'
  refine SegWS.post_run (SegWS.pre_run (P' := PE) (SegWS.exists_pre fun G => ?_) fun s c fs' h => ⟨?_, ?_⟩)
  · obtain ⟨mC, σC, cC, cE, fr, g⟩ := G
    by_cases hG : nC.J σC cC ∧ CallTo p cC cE fr ∧ (Ne g fr).J (enter kc σC) cE
    · refine (hcallee R' (F' (mC, σC, cC, cE, fr, g)) hR' hal' (Int.le_refl _) (Int.le_refl _) (hF' _)
        (fun hc => hK' hc _) (fun _ h => h.1) rfl (fun m hm k hk hn => by
          obtain ⟨j, hj, -⟩ := hm.2.2.1.slot k hk
          rw [hm.2.1 k hk hn, hj]; rfl) g fr ⟨σC, cC, cE, hG⟩
        (fun m hm => ⟨mC, σC, cC, cE, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2, hm.2.1⟩)).mono_post ?_
      rintro s c fs' (⟨⟨x, ⟨he, hn, hdc, hpc, σx, hAx, ⟨hD, hDF, hAC, hJC, hCT, hJE⟩, hJx⟩, hM⟩, rfl⟩ | hab)
      rotate_left
      · exact Pend.of (.inr hab)
      simp only at hDF hAC hJC hCT hJE
      have hAR : Abs R ⟨kc + (Ex g fr x).o.sp, []⟩ s.st.1 (leave R' kc σC σx) := by
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
            · rw [hDF k hk hin]
              exact hj
            · simp only [leave]; rw [ite_eq_right hin]; exact hv
      obtain ⟨c'', hrun, hL⟩ := hret g x σC cC cE fr σx c (leave R' kc σC σx) hJC hCT hJE hJx rfl rfl
        (fun k _ hn => by simp only [leave]; exact ite_eq_right hn)
      have hs : s = { s with st := (s.st.1, (Ex g fr x).pc) } := by rw [← hpc]; rfl
      refine ⟨c'', fs, hrun, .inl ⟨?_, rfl⟩⟩
      rw [hs]
      rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
      · exact .inl ⟨j, hj.at he hn hdc hAR (hF₂ _ hD hM)⟩
      · exact .inr ⟨y, hy.at he hn hdc hAR (hF₂ _ hD hM)⟩
    · exact SegWS.empty fun s c fs' ⟨⟨_, _, _, _, _, _, ⟨_, _, _, hJC, hCT, hJE⟩, _⟩, _⟩ => hG ⟨hJC, hCT, hJE⟩
  · obtain ⟨hA, rfl⟩ := h
    exact hWC s c hA
  · obtain ⟨⟨he, hn, hdc, hpc, σC, hA, hD, hJ⟩, rfl⟩ := h
    obtain ⟨g, cE, fr, hCT, hgpc, hgJ⟩ := hent σC c hJ
    refine ⟨cE, fr :: _, .single (hCT.step _), (s.st.1, σC, c, cE, fr, g), ⟨he, hn, hdc, by rw [hpc, hgpc],
      enter kc σC, ?_, ⟨hD, fun _ _ _ => rfl, hA, hJ, hCT, hgJ⟩, hgJ⟩, rfl⟩
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

open Classical in
/-- **A source call node whose callee may abort** (`call_ndS` with an
abort postcondition `Ab`): the callee's specification ends either at its
exits at `fr :: fs` or in `Ab` (at any frames: e.g. a stack-depth abort
deep in the callee), and so does the call node's segment. As `call_ndS`: At the caller's frames `fs`, from the call node `nC` (`hent`: its
source control calls, `CallTo`, and the callee's entry node holds at the
callee's control) to the caller's nodes, the return taken (`hret`: the
source runs from the callee's exit control at `fr :: fs` back to the
caller's frames). The callee's specification (`hcallee`) is a segment at
the frames `fr :: fs`, with `call_nd_FWK`'s regions and frame conditions.
`hWC`: `W` holds at the call node's pairs. -/
theorem call_ndSA {KC : Prop} {W : FragS isaLSE2} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {nC : ND} {γ : Type _} {κ' : Sort _} {lo' hi' : Int} {Ne : γ → ND} {Ex : γ → κ' → ND}
    {fs : List TermRun.Frame} {Ab : FragS isaLSE2}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp + lo') (hlo0 : lo' ≤ 0) (hkc : nC.o.sp < R.hi) (hhi0 : hi' ≤ 0)
    (hk16 : nC.o.sp % 16 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hFK : KC → KStable K F)
    (hKR : KC → ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hF₂ : ∀ m, F m → M m → F₂ m)
    (hWC : ∀ s c, At exe endPc R F nC s c → W s c fs)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ lo' →
      hi' ≤ R'.hi → FStable R' F' → (KC → KStable K F') → (∀ m, F' m → F m) → R' = R.callee nC.o.sp lo' hi' →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - nC.o.sp) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g (fr : TermRun.Frame),
        (∃ σC c cE, nC.J σC c ∧ CallTo p c cE fr ∧ (Ne g).J (enter nC.o.sp σC) cE) →
        (∀ m, F' m → ∃ mC σC c cE, Abs R nC.o mC σC ∧ nC.J σC c ∧ CallTo p c cE fr ∧
          (Ne g).J (enter nC.o.sp σC) cE ∧
          ∀ k, R.Off k → ¬ R'.Off (k - nC.o.sp) → Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegWS W K p lbl ms ((At exe endPc R' F' (Ne g)).at (fr :: fs))
          (fun s c fs' => Frag.at (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c ∧ M s.st.1) (fr :: fs) s c fs' ∨
            Ab s c fs'))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g cE fr, CallTo p c cE fr ∧ (Ne g).pc = nC.pc ∧ (Ne g).J (enter nC.o.sp σC) cE)
    (hret : ∀ g x σC c cE fr σx c' (σR : AS), nC.J σC c → CallTo p c cE fr → (Ne g).J (enter nC.o.sp σC) cE →
      (Ex g x).J σx c' → σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      ∃ c'', FrameRun p (c', fr :: fs) (c'', fs) ∧ Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp + (Ex g x).o.sp, []⟩, σR⟩ c'') :
    SegWS W K p lbl ms ((At exe endPc R F nC).at fs)
      (fun s c fs' => (Next exe endPc R F₂ N E).at fs s c fs' ∨ Ab s c fs')  :=
  call_ndSF (Ne := fun g _ => Ne g) (Ex := fun g _ x => Ex g x) hR hal hF hlo hlo0 hkc hhi0 hk16 hl8 hh8 hFK hKR hF₂
    hWC hcallee (fun g _ => hNe g) hent hret

end Fn

end Spike.Lib.A64.Flow
