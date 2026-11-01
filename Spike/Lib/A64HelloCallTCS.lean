/-
**A source call inside a frame-aware fragment** (AArch64): `A64CallS.call_ndSG`'s source call over
`Spike/Lib/HelloSegTCS.lean`'s `SegTCS` (the worker's segments at any call
depth, their invariant inside a fragment `S`), so hello's worker's call of
`print` (the frame `uFrame` pushed) is one `SegTCS` segment at the worker's
frames.

At the call node `nC` (after the caller's `bl`) the caller's source is at
`let x = call f a in e` (`CallTo`). The callee's first row takes the
source's call (`SegTCS.pre_run`); its exits take the return
(`SegTCS.post_run`, `hret`: a frame run from `fr :: fs` back to `fs`). The
callee's specification (`hcallee`) is a `SegTCS` segment at `fr :: fs`
from its entry to its exits, at `call_ndS`'s regions and frame conditions
(no kernel closure `K`: `SegTCS` has no outside move). `hWC`: `S` at the
call node's pairs (they join the invariant).

- `CallToI`, `CallGFI`, `CallGFI.ret`: `CallTo`, `CallGF`, `CallGF.ret` at
  any index arguments (hello's `call print [q] sl`).
- `call_ndTCS`: the call node, a `SegTCS` segment at `fs` to the caller's
  nodes.
-/
import Spike.Lib.A64CallS
import Spike.Lib.HelloSegTCS

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.HelloSegTCS (SegTCS)

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A source call at any index arguments** (`CallTo` with `is` free;
`FrameStep.call` ignores them): hello's `let u = call print [q] sl in e`. -/
def CallToI (p : Prog) (c cE : Ctl) (fr : TermRun.Frame) : Prop :=
  ∃ (x f : String) (is : List String) (a : CoreTerm.At) (e : Expr) (d : Decl) (t : Ty) (ws : List TermRun.Word),
    c.term = .let_ x (.call f is a []) e ∧ p.find? (·.name == f) = some d ∧
    TermRun.evalAt c.env a = some (t, ws) ∧ cE = ⟨d.body, [(d.arg, d.argTy, ws)], none⟩ ∧
    fr = ⟨x, e, c.env, [], d.retTy⟩

/-- A source call at any index arguments is a frame step. -/
theorem CallToI.step {p : Prog} {c cE : Ctl} {fr : TermRun.Frame} (h : CallToI p c cE fr)
    (fs : List TermRun.Frame) : FrameStep p (c, fs) (cE, fr :: fs) := by
  obtain ⟨x, f, is, a, e, d, t, ws, ht, hd, ha, rfl, rfl⟩ := h
  exact .call ht hd ha

/-- `CallTo` is `CallToI` at `is = []`. -/
theorem CallTo.toI {p : Prog} {c cE : Ctl} {fr : TermRun.Frame} (h : CallTo p c cE fr) : CallToI p c cE fr :=
  let ⟨x, f, a, e, d, t, ws, h⟩ := h
  ⟨x, f, [], a, e, d, t, ws, h⟩

/-- **The callee's ghost frame condition at a source call** (`CallGF` at `CallToI`):
at the ghost `G` (the machine data `G.1` and abstract state `G.2.1` at the
call node `nC`, the caller's control `G.2.2.1`, the callee's entry control
`G.2.2.2.1` and frame `G.2.2.2.2.1`, the callee's parameters `G.2.2.2.2.2`),
the caller's `F`, the caller's cells outside the callee's region
`R.callee kc lo' hi'` as in `G.1`, the caller's state at `nC` (`Abs`,
`nC.J`), its control calling (`CallTo`) and the callee's entry node holding
at the callee's control. -/
def CallGFI {γ : Type _} (p : Prog) (R : Region) (F : MachineData → Prop) (nC : ND) (lo' hi' : Int)
    (Ne : γ → ND) (G : MachineData × AS × Ctl × Ctl × TermRun.Frame × γ) (m : MachineData) : Prop :=
  F m ∧ (∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) →
      Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt G.1.dmem (R.addr k) 8) ∧
    Abs R nC.o G.1 G.2.1 ∧ nC.J G.2.1 G.2.2.1 ∧ CallToI p G.2.2.1 G.2.2.2.1 G.2.2.2.2.1 ∧
    (Ne G.2.2.2.2.2).J (enter nC.o.sp G.2.1) G.2.2.2.1

/-- **The return to the caller from an exit under the ghost frame
condition** (`CallGF.ret` at `CallToI`): at an exit `Ex g x` of the callee in its
region, its frame condition `CallGFI` at the ghost `G`, the source runs from
the callee's control at the frames `G`'s frame `:: fs` back to `fs`
(`hret`), landing at a caller's node at `F₂` (the caller's abstract state
rebuilt as `leave` of the call's and the exit's). -/
theorem CallGFI.ret {F₂ : MachineData → Prop} {nC : ND} {γ : Type _} {κ' : Sort _} {lo' hi' : Int}
    {Ne : γ → ND} {Ex : γ → κ' → ND} {fs : List TermRun.Frame}
    (hret : ∀ g x σC c cE fr σx c' (σR : AS), nC.J σC c → CallToI p c cE fr → (Ne g).J (enter nC.o.sp σC) cE →
      (Ex g x).J σx c' → σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      ∃ c'', FrameRun p (c', fr :: fs) (c'', fs) ∧ Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp + (Ex g x).o.sp, []⟩, σR⟩ c'')
    {G : MachineData × AS × Ctl × Ctl × TermRun.Frame × γ} {x : κ'} {s : State} {c : Ctl}
    (hAt : At exe endPc (R.callee nC.o.sp lo' hi') (CallGFI p R F nC lo' hi' Ne G) (Ex G.2.2.2.2.2 x) s c)
    (hF₂ : F₂ s.st.1) :
    ∃ c'', FrameRun p (c, G.2.2.2.2.1 :: fs) (c'', fs) ∧ Next exe endPc R F₂ N E s c'' := by
  obtain ⟨mC, σC, cC, cE, fr, g⟩ := G
  obtain ⟨he, hn, hdc, hpc, σx, hAx, ⟨-, hDF, hAC, hJC, hCT, hJE⟩, hJx⟩ := hAt
  let kc := nC.o.sp
  let R' := R.callee kc lo' hi'
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
        · rw [hDF k hk hin]
          exact hj
        · simp only [leave]; rw [ite_eq_right hin]; exact hv
  obtain ⟨c'', hrun, hL⟩ := hret g x σC cC cE fr σx c (leave R' kc σC σx) hJC hCT hJE hJx rfl rfl
    (fun k _ hn => by simp only [leave]; exact ite_eq_right hn)
  have hs : s = { s with st := (s.st.1, (Ex g x).pc) } := by rw [← hpc]
  refine ⟨c'', hrun, ?_⟩
  rw [hs]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hAR hF₂⟩
  · exact .inr ⟨y, hy.at he hn hdc hAR hF₂⟩

open Classical in
/-- **A source call node inside `S`** (`call_ndSG` over `SegTCS`): at the
caller's frames `fs`, from the call node `nC` (`hent`: its source control
calls, `CallTo`, and the callee's entry node holds at the callee's control)
to the caller's nodes, the return taken (`hret`). The callee's
specification (`hcallee`) is a `SegTCS` segment at the frames `fr :: fs`
with `call_ndS`'s regions and frame conditions; `hWC`: `S` at the call
node's pairs. -/
theorem call_ndTCS {S : FragS isaLSE2} {nC : ND} {γ : Type _} {κ' : Sort _} {lo' hi' : Int} {Ne : γ → ND}
    {Ex : γ → κ' → ND} {fs : List TermRun.Frame}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp + lo') (hlo0 : lo' ≤ 0) (hkc : nC.o.sp < R.hi) (hhi0 : hi' ≤ 0)
    (hk16 : nC.o.sp % 16 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hWC : ∀ s c, At exe endPc R F nC s c → S s c fs)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ lo' →
      hi' ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → R' = R.callee nC.o.sp lo' hi' →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - nC.o.sp) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g (fr : TermRun.Frame),
        (∃ σC c cE, nC.J σC c ∧ CallToI p c cE fr ∧ (Ne g).J (enter nC.o.sp σC) cE) →
        (∀ m, F' m → ∃ mC σC c cE, Abs R nC.o mC σC ∧ nC.J σC c ∧ CallToI p c cE fr ∧
          (Ne g).J (enter nC.o.sp σC) cE ∧
          ∀ k, R.Off k → ¬ R'.Off (k - nC.o.sp) → Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegTCS S p lbl ms ((At exe endPc R' F' (Ne g)).at (fr :: fs))
          (Frag.at (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c) (fr :: fs)))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g cE fr, CallToI p c cE fr ∧ (Ne g).pc = nC.pc ∧ (Ne g).J (enter nC.o.sp σC) cE)
    (hret : ∀ g x σC c cE fr σx c' (σR : AS), nC.J σC c → CallToI p c cE fr → (Ne g).J (enter nC.o.sp σC) cE →
      (Ex g x).J σx c' → σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      ∃ c'', FrameRun p (c', fr :: fs) (c'', fs) ∧ Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp + (Ex g x).o.sp, []⟩, σR⟩ c'') :
    SegTCS S p lbl ms ((At exe endPc R F nC).at fs) ((Next exe endPc R F N E).at fs) := by
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
  refine SegTCS.post_run (SegTCS.pre_run (P' := PE) (SegTCS.exists_pre fun G => ?_) fun s c fs' h => ⟨?_, ?_⟩)
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
    · exact SegTCS.empty fun s c fs' ⟨⟨_, _, _, _, _, _, ⟨_, _, _, hJC, hCT, hJE⟩, _⟩, _⟩ => hG ⟨hJC, hCT, hJE⟩
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

end Fn

end Spike.Lib.A64.Flow

/-- info: 'Spike.Lib.A64.Flow.call_ndTCS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.call_ndTCS
