/-
**A source call inside a frame-aware fragment, landing in `X`** (hello.w, row 5j-wit-W; AArch64): `call_ndTCS`
(`Spike/Lib/A64HelloCallTCS.lean`) over `Spike/Lib/HelloSegTCSX.lean`'s `SegTCSX`, so a segment through hello's
worker's call of `print` has every landing pair in the landing fragment `X`.

Release note: when the `X` chain replaces the `SegTCS` one, `call_ndTCS` becomes a one-line corollary through
`SegTCSX.toS` (at `X := S`) or is deleted; the release keeps one chain.

- `call_ndTCSX`: the call node, a `SegTCSX` segment at `fs` to the caller's nodes; `X` at the call node's pairs
  (`hXC`) and the callee's segment a `SegTCSX` one.
-/
import Spike.Lib.A64HelloCallTCS
import Spike.Lib.HelloSegTCSXC

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.HelloSegTCSX (SegTCSX)

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

open Classical in
/-- **A source call node inside `S`, landing in `X`** (`call_ndTCS` over `SegTCSX`): as `call_ndTCS`, the
callee's specification (`hcallee`) a `SegTCSX` segment at `fr :: fs`; `hXC`: `X` at the call node's pairs (the
callee's entry row lands from them through the source's call). The return's frame run adds no landing pair:
the callee's exits are landed by its own rows, in `X`. -/
theorem call_ndTCSX {S X : FragS isaLSE2} {nC : ND} {γ : Type _} {κ' : Sort _} {lo' hi' : Int} {Ne : γ → ND}
    {Ex : γ → κ' → ND} {fs : List TermRun.Frame}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp + lo') (hlo0 : lo' ≤ 0) (hkc : nC.o.sp < R.hi) (hhi0 : hi' ≤ 0)
    (hk16 : nC.o.sp % 16 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hWC : ∀ s c, At exe endPc R F nC s c → S s c fs) (hXC : ∀ s c, At exe endPc R F nC s c → X s c fs)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ lo' →
      hi' ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → R' = R.callee nC.o.sp lo' hi' →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - nC.o.sp) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g (fr : TermRun.Frame),
        (∃ σC c cE, nC.J σC c ∧ CallToI p c cE fr ∧ (Ne g).J (enter nC.o.sp σC) cE) →
        (∀ m, F' m → ∃ mC σC c cE, Abs R nC.o mC σC ∧ nC.J σC c ∧ CallToI p c cE fr ∧
          (Ne g).J (enter nC.o.sp σC) cE ∧
          ∀ k, R.Off k → ¬ R'.Off (k - nC.o.sp) → Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegTCSX S X p lbl ms ((At exe endPc R' F' (Ne g)).at (fr :: fs))
          (Frag.at (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c) (fr :: fs)))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g cE fr, CallToI p c cE fr ∧ (Ne g).pc = nC.pc ∧ (Ne g).J (enter nC.o.sp σC) cE)
    (hret : ∀ g x σC c cE fr σx c' (σR : AS), nC.J σC c → CallToI p c cE fr → (Ne g).J (enter nC.o.sp σC) cE →
      (Ex g x).J σx c' → σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      ∃ c'', FrameRun p (c', fr :: fs) (c'', fs) ∧ Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp + (Ex g x).o.sp, []⟩, σR⟩ c'') :
    SegTCSX S X p lbl ms ((At exe endPc R F nC).at fs) ((Next exe endPc R F N E).at fs) := by
  let kc := nC.o.sp
  let R' := R.callee kc lo' hi'
  have hR' : R'.OK := Region.callee_ok hR hlo hlo0 hkc (by omega)
  have hb' := Region.callee_base (hi' := hi') hR hlo hlo0 hkc
  have hal' : R'.base.toNat % 16 = 0 := by
    have : ((R'.base.toNat : Int)) % 16 = 0 := by rw [hb']; omega
    omega
  have hFR' : FStable R' F := FStable.callee hR hlo hlo0 hkc (by omega) hF
  let F' := CallGFI p R F nC lo' hi' Ne
  have hF' : ∀ G, FStable R' (F' G) := fun G m m' hm hd =>
    ⟨hFR' m m' hm.1 hd, fun k hk hn =>
      (hd _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkc (by omega) hl8 hh8 hk hn)).trans
        (hm.2.1 k hk hn), hm.2.2⟩
  let PE : FragS isaLSE2 := fun s c fs' =>
    ∃ G : MachineData × AS × Ctl × Ctl × TermRun.Frame × γ,
      (At exe endPc R' (F' G) (Ne G.2.2.2.2.2)).at (G.2.2.2.2.1 :: fs) s c fs'
  refine SegTCSX.post_run (SegTCSX.pre_run (P' := PE) (SegTCSX.exists_pre fun G => ?_) fun s c fs' h => ⟨?_, ?_, ?_⟩)
  · obtain ⟨mC, σC, cC, cE, fr, g⟩ := G
    by_cases hG : nC.J σC cC ∧ CallToI p cC cE fr ∧ (Ne g).J (enter kc σC) cE
    · refine (hcallee R' (F' (mC, σC, cC, cE, fr, g)) hR' hal' (Int.le_refl _) (Int.le_refl _) (hF' _)
        (fun _ h => h.1) rfl (fun m hm k hk hn => by
          obtain ⟨j, hj, -⟩ := hm.2.2.1.slot k hk
          rw [hm.2.1 k hk hn, hj]; rfl) g fr ⟨σC, cC, cE, hG⟩
        (fun m hm => ⟨mC, σC, cC, cE, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2, hm.2.1⟩)).mono_post ?_
      rintro s c fs' ⟨⟨x, hAt⟩, rfl⟩
      have hD : F s.st.1 := by obtain ⟨-, -, -, -, -, -, hD, -⟩ := hAt; exact hD.1
      obtain ⟨c'', hrun, hN⟩ := CallGFI.ret (F₂ := F) (fs := fs) hret hAt hD
      exact ⟨c'', fs, hrun, hN, rfl⟩
    · exact SegTCSX.empty fun s c fs' ⟨⟨_, _, _, _, _, _, ⟨_, _, _, hJC, hCT, hJE⟩, _⟩, _⟩ => hG ⟨hJC, hCT, hJE⟩
  · obtain ⟨hA, rfl⟩ := h
    exact hWC s c hA
  · obtain ⟨hA, rfl⟩ := h
    exact hXC s c hA
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

end Fn

end Spike.Lib.A64.Flow

/-- info: 'Spike.Lib.A64.Flow.call_ndTCSX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.call_ndTCSX
