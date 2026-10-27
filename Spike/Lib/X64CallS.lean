/-
**Source calls on X64**: a call node whose callee runs its own source
body in a pushed frame (`call_ndS`), the twin of `call_nd_FWK`
(`Spike/Lib/X64Call.lean`) over segments with frames (`Spike/Lib/SegS.lean`).

At the call node `nC` (after the caller's `call`: the pc at the callee's
entry offset `e0`, the return address pushed on the stack) the caller's source is at
`let x = call f a in e` (`CallTo`). The callee's first instruction takes the
source's call (`FrameStep.call`): the callee's body at its argument, with
the frame returning into `x` pushed. The callee's specification is a
segment at the frames `fr :: fs` from its entry to its exits; at an exit
the source still has the callee's frame, and the row landing there takes its
return (`hret`: a frame run to the caller's frames, `SegWS.post_run`); the
call is taken with the callee's first row (`SegWS.pre_run`), so neither the
call's nor the return's pending pairs join the invariant.

The machine side (regions, frame conditions, the abstract state seen from
the callee) is `call_nd_FWK`'s.
-/
import Spike.Lib.X64Call
import Spike.Lib.SegS

namespace Spike.Lib.X64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64

/-- **A source call**: the control `c` is at `let x = call f a in e` of a
code block `f` of `p` with no type or index arguments; the callee starts at
`cE` (its body, its argument bound to `a`'s words at its declared type) with
the frame `fr` (returning into `x` and then `e`, in `c`'s environment)
pushed. -/
def CallTo (p : Prog) (c cE : Ctl) (fr : TermRun.Frame) : Prop :=
  ∃ (x f : String) (a : CoreTerm.At) (e : Expr) (d : Decl) (t : Ty) (ws : List TermRun.Word),
    c.term = .let_ x (.call f [] a []) e ∧ p.find? (·.name == f) = some d ∧
    TermRun.evalAt c.env a = some (t, ws) ∧ cE = ⟨d.body, [(d.arg, d.argTy, ws)], none⟩ ∧
    fr = ⟨x, e, c.env, [], d.retTy⟩

/-- A source call is a frame step. -/
theorem CallTo.step {p : Prog} {c cE : Ctl} {fr : TermRun.Frame} (h : CallTo p c cE fr) (fs : List TermRun.Frame) :
    FrameStep p (c, fs) (cE, fr :: fs) := by
  obtain ⟨x, f, a, e, d, t, ws, ht, hd, ha, rfl, rfl⟩ := h
  exact .call ht hd ha

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **The callee's ghost frame condition at a source call** (`call_ndS`'s):
at the ghost `G` (the machine data `G.1` and abstract state `G.2.1` at the
call node `nC`, the caller's control `G.2.2.1`, the callee's entry control
`G.2.2.2.1` and frame `G.2.2.2.2.1`, the callee's parameters `G.2.2.2.2.2`),
the caller's `F`, the caller's cells outside the callee's region
`R.callee kc lo' hi'` as in `G.1`, the caller's state at `nC` (`Abs`,
`nC.J`), its control calling (`CallTo`) and the callee's entry node holding
at the callee's control. -/
def CallGF {γ : Type _} (p : Prog) (R : Region) (F : MachineData → Prop) (nC : ND) (e0 : Int) (lo' hi' : Int)
    (Ne : γ → ND) (G : MachineData × AS × Ctl × Ctl × TermRun.Frame × γ) (m : MachineData) : Prop :=
  F m ∧ (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) →
      Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt G.1.dmem (R.addr k) 8) ∧
    Abs R nC.o G.1 G.2.1 ∧ nC.J G.2.1 G.2.2.1 ∧ CallTo p G.2.2.1 G.2.2.2.1 G.2.2.2.2.1 ∧
    (Ne G.2.2.2.2.2).J (enter (nC.o.sp - e0) G.2.1) G.2.2.2.1

/-- **The return to the caller from an exit under the ghost frame
condition** (`call_ndS`'s return): at an exit `Ex g x` of the callee in its
region, its frame condition `CallGF` at the ghost `G`, the source runs from
the callee's control at the frames `G`'s frame `:: fs` back to `fs`
(`hret`), landing at a caller's node at `F₂` (the caller's abstract state
rebuilt as `leave` of the call's and the exit's). -/
theorem CallGF.ret {F₂ : MachineData → Prop} {nC : ND} {γ : Type _} {κ' : Sort _} {e0 lo' hi' : Int}
    {Ne : γ → ND} {Ex : γ → κ' → ND} {fs : List TermRun.Frame}
    (hret : ∀ g x σC c cE fr σx c' (σR : AS), nC.J σC c → CallTo p c cE fr → (Ne g).J (enter (nC.o.sp - e0) σC) cE →
      (Ex g x).J σx c' → σR.regs = σx.regs → σR.zmms = σx.zmms → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) → σR.slot k = σC.slot k) →
      ∃ c'', FrameRun p (c', fr :: fs) (c'', fs) ∧ Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp - e0 + (Ex g x).o.sp, []⟩, σR⟩ c'')
    {G : MachineData × AS × Ctl × Ctl × TermRun.Frame × γ} {x : κ'} {s : State} {c : Ctl}
    (hAt : At exe endPc (R.callee (nC.o.sp - e0) lo' hi') (CallGF p R F nC e0 lo' hi' Ne G) (Ex G.2.2.2.2.2 x) s c)
    (hF₂ : F₂ s.st.1) :
    ∃ c'', FrameRun p (c, G.2.2.2.2.1 :: fs) (c'', fs) ∧ Next exe endPc R F₂ N E s c'' := by
  obtain ⟨mC, σC, cC, cE, fr, g⟩ := G
  obtain ⟨he, hn, hdc, hpc, σx, hAx, ⟨-, hDF, hAC, hJC, hCT, hJE⟩, hJx⟩ := hAt
  let kc := (nC.o.sp - e0)
  let R' := R.callee kc lo' hi'
  have hAR : Abs R ⟨kc + (Ex g x).o.sp, []⟩ s.st.1 (leave R' kc σC σx) := by
    refine ⟨hAx.regs, hAx.zmms, hAx.status, ?_, fun k hk => ?_⟩
    · intro r k' hr
      obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
      have := hAx.so .rsp (Ex g x).o.sp (by simp [SO.get])
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
  obtain ⟨c'', hrun, hL⟩ := hret g x σC cC cE fr σx c (leave R' kc σC σx) hJC hCT hJE hJx rfl rfl rfl
    (fun k _ hn => by simp only [leave]; exact ite_eq_right hn)
  have hs : s = { s with st := (s.st.1, (Ex g x).pc) } := by rw [← hpc]
  refine ⟨c'', hrun, ?_⟩
  rw [hs]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hAR hF₂⟩
  · exact .inr ⟨y, hy.at he hn hdc hAR hF₂⟩

open Classical in
/-- **A source call node inside `W`, its callee at the ghost frame
condition** (`call_ndS` with more for the callee): the callee's
specification (`hcallee`) may assume its frame condition `F'` is the call's
ghost frame condition `CallGF` at a ghost `G` whose frame and parameters are
the call's (e.g. for the callee to record the suspended caller, whose state
`G` carries); `call_ndS` is this at a callee's specification for every
`F'`. -/
theorem call_ndSG {KC : Prop} {W : FragS isa} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {nC : ND} {γ : Type _} {κ' : Sort _} {e0 lo' hi' : Int} {Ne : γ → ND} {Ex : γ → κ' → ND}
    {fs : List TermRun.Frame}
    (hR : R.OK) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp - e0 + lo') (hlo0 : lo' ≤ 0) (hkb : nC.o.sp - e0 < R.hi)
    (hhi : nC.o.sp - e0 + hi' ≤ R.hi) (hk8 : (nC.o.sp - e0) % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hFK : KC → KStable K F)
    (hKR : KC → ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hF₂ : ∀ m, F m → M m → F₂ m)
    (hWC : ∀ s c, At exe endPc R F nC s c → W s c fs)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ lo' →
      hi' ≤ R'.hi → FStable R' F' → (KC → KStable K F') → (∀ m, F' m → F m) → R' = R.callee (nC.o.sp - e0) lo' hi' →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - (nC.o.sp - e0)) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g (fr : TermRun.Frame),
        (∃ G, F' = CallGF p R F nC e0 lo' hi' Ne G ∧ G.2.2.2.2.1 = fr ∧ G.2.2.2.2.2 = g) →
        (∃ σC c cE, nC.J σC c ∧ CallTo p c cE fr ∧ (Ne g).J (enter (nC.o.sp - e0) σC) cE) →
        (∀ m, F' m → ∃ mC σC c cE, Abs R nC.o mC σC ∧ nC.J σC c ∧ CallTo p c cE fr ∧
          (Ne g).J (enter (nC.o.sp - e0) σC) cE ∧
          ∀ k, R.Off k → ¬ R'.Off (k - (nC.o.sp - e0)) → Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegWS W K p lbl ms ((At exe endPc R' F' (Ne g)).at (fr :: fs))
          (Frag.at (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c ∧ M s.st.1) (fr :: fs)))
    (hNe : ∀ g, (Ne g).o = ⟨e0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g cE fr, CallTo p c cE fr ∧ (Ne g).pc = nC.pc ∧ (Ne g).J (enter (nC.o.sp - e0) σC) cE)
    (hret : ∀ g x σC c cE fr σx c' (σR : AS), nC.J σC c → CallTo p c cE fr → (Ne g).J (enter (nC.o.sp - e0) σC) cE →
      (Ex g x).J σx c' → σR.regs = σx.regs → σR.zmms = σx.zmms → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) → σR.slot k = σC.slot k) →
      ∃ c'', FrameRun p (c', fr :: fs) (c'', fs) ∧ Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp - e0 + (Ex g x).o.sp, []⟩, σR⟩ c'') :
    SegWS W K p lbl ms ((At exe endPc R F nC).at fs) ((Next exe endPc R F₂ N E).at fs) := by
  let kc := nC.o.sp - e0
  let R' := R.callee kc lo' hi'
  have hR' : R'.OK := Region.callee_ok hR hlo hlo0 hkb hhi
  have hFR' : FStable R' F := FStable.callee hR hlo hlo0 hkb hhi hF
  let F' := CallGF p R F nC e0 lo' hi' Ne
  have hF' : ∀ G, FStable R' (F' G) := fun G m m' hm hd =>
    ⟨hFR' m m' hm.1 hd, fun k hk hn =>
      (hd _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkb hk8 hl8 hh8 hk hn)).trans
        (hm.2.1 k hk hn), hm.2.2⟩
  have hK' : KC → ∀ G, KStable K (F' G) := fun hc G s s' hk hm =>
    ⟨hFK hc s s' hk hm.1, fun k hk' hn => (hKR hc s s' hk hm.1 k hk' hn).trans (hm.2.1 k hk' hn), hm.2.2⟩
  let PE : FragS isa := fun s c fs' =>
    ∃ G : MachineData × AS × Ctl × Ctl × TermRun.Frame × γ,
      (At exe endPc R' (F' G) (Ne G.2.2.2.2.2)).at (G.2.2.2.2.1 :: fs) s c fs'
  refine SegWS.post_run (SegWS.pre_run (P' := PE) (SegWS.exists_pre fun G => ?_) fun s c fs' h => ⟨?_, ?_⟩)
  · obtain ⟨mC, σC, cC, cE, fr, g⟩ := G
    by_cases hG : nC.J σC cC ∧ CallTo p cC cE fr ∧ (Ne g).J (enter kc σC) cE
    · refine (hcallee R' (F' (mC, σC, cC, cE, fr, g)) hR' (Int.le_refl _) (Int.le_refl _) (hF' _)
        (fun hc => hK' hc _) (fun _ h => h.1) rfl (fun m hm k hk hn => by
          obtain ⟨j, hj, -⟩ := hm.2.2.1.slot k hk
          rw [hm.2.1 k hk hn, hj]; rfl) g fr ⟨_, rfl, rfl, rfl⟩ ⟨σC, cC, cE, hG⟩
        (fun m hm => ⟨mC, σC, cC, cE, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2, hm.2.1⟩)).mono_post ?_
      rintro s c fs' ⟨⟨x, hAt, hM⟩, rfl⟩
      have hD : F s.st.1 := by obtain ⟨-, -, -, -, -, -, hD, -⟩ := hAt; exact hD.1
      obtain ⟨c'', hrun, hN⟩ := CallGF.ret (F₂ := F₂) (fs := fs) hret hAt (hF₂ _ hD hM)
      exact ⟨c'', fs, hrun, hN, rfl⟩
    · exact SegWS.empty fun s c fs' ⟨⟨_, _, _, _, _, _, ⟨_, _, _, hJC, hCT, hJE⟩, _⟩, _⟩ => hG ⟨hJC, hCT, hJE⟩
  · obtain ⟨hA, rfl⟩ := h
    exact hWC s c hA
  · obtain ⟨⟨he, hn, hdc, hpc, σC, hA, hD, hJ⟩, rfl⟩ := h
    obtain ⟨g, cE, fr, hCT, hgpc, hgJ⟩ := hent σC c hJ
    refine ⟨cE, fr :: _, .single (hCT.step _), (s.st.1, σC, c, cE, fr, g), ⟨he, hn, hdc, by rw [hpc, hgpc],
      enter kc σC, ?_, ⟨hD, fun _ _ _ => rfl, hA, hJ, hCT, hgJ⟩, hgJ⟩, rfl⟩
    rw [hNe]
    refine ⟨hA.regs, hA.zmms, hA.status, ?_, fun k hk => ?_⟩
    · intro r k' hr
      obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
      have := hA.so .rsp nC.o.sp (by simp [SO.get])
      simp only [enter] at this ⊢
      rw [this, Region.callee_addr]; congr 1; omega
    · obtain ⟨j, hj, hv⟩ := hA.slot _ (Region.callee_off hlo hhi hk8 hk)
      exact ⟨j, by rw [Region.callee_addr]; exact hj, hv⟩

open Classical in
/-- **A source call node inside `W`, closed under `K` when `KC`, with a
memory postcondition**: `call_nd_FWK` with the callee's body run in a pushed
frame. At the caller's frames `fs`, from the call node `nC` (`hent`: its
source control calls, `CallTo`, and the callee's entry node holds at the
callee's control) to the caller's nodes, the return taken (`hret`: the
source runs from the callee's exit control at `fr :: fs` back to the
caller's frames). The callee's specification (`hcallee`) is a segment at
the frames `fr :: fs`, with `call_nd_FWK`'s regions and frame conditions.
`hWC`: `W` holds at the call node's pairs. -/
theorem call_ndS {KC : Prop} {W : FragS isa} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {nC : ND} {γ : Type _} {κ' : Sort _} {e0 lo' hi' : Int} {Ne : γ → ND} {Ex : γ → κ' → ND}
    {fs : List TermRun.Frame}
    (hR : R.OK) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp - e0 + lo') (hlo0 : lo' ≤ 0) (hkb : nC.o.sp - e0 < R.hi)
    (hhi : nC.o.sp - e0 + hi' ≤ R.hi) (hk8 : (nC.o.sp - e0) % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hFK : KC → KStable K F)
    (hKR : KC → ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hF₂ : ∀ m, F m → M m → F₂ m)
    (hWC : ∀ s c, At exe endPc R F nC s c → W s c fs)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ lo' →
      hi' ≤ R'.hi → FStable R' F' → (KC → KStable K F') → (∀ m, F' m → F m) → R' = R.callee (nC.o.sp - e0) lo' hi' →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - (nC.o.sp - e0)) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g (fr : TermRun.Frame),
        (∃ σC c cE, nC.J σC c ∧ CallTo p c cE fr ∧ (Ne g).J (enter (nC.o.sp - e0) σC) cE) →
        (∀ m, F' m → ∃ mC σC c cE, Abs R nC.o mC σC ∧ nC.J σC c ∧ CallTo p c cE fr ∧
          (Ne g).J (enter (nC.o.sp - e0) σC) cE ∧
          ∀ k, R.Off k → ¬ R'.Off (k - (nC.o.sp - e0)) → Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegWS W K p lbl ms ((At exe endPc R' F' (Ne g)).at (fr :: fs))
          (Frag.at (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c ∧ M s.st.1) (fr :: fs)))
    (hNe : ∀ g, (Ne g).o = ⟨e0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g cE fr, CallTo p c cE fr ∧ (Ne g).pc = nC.pc ∧ (Ne g).J (enter (nC.o.sp - e0) σC) cE)
    (hret : ∀ g x σC c cE fr σx c' (σR : AS), nC.J σC c → CallTo p c cE fr → (Ne g).J (enter (nC.o.sp - e0) σC) cE →
      (Ex g x).J σx c' → σR.regs = σx.regs → σR.zmms = σx.zmms → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) → σR.slot k = σC.slot k) →
      ∃ c'', FrameRun p (c', fr :: fs) (c'', fs) ∧ Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp - e0 + (Ex g x).o.sp, []⟩, σR⟩ c'') :
    SegWS W K p lbl ms ((At exe endPc R F nC).at fs) ((Next exe endPc R F₂ N E).at fs) :=
  call_ndSG hR hF hlo hlo0 hkb hhi hk8 hl8 hh8 hFK hKR hF₂ hWC
    (fun R' F' h1 h2 h3 h4 h5 h6 h7 h8 g fr _ => hcallee R' F' h1 h2 h3 h4 h5 h6 h7 h8 g fr) hNe hent hret

open Classical in
/-- **A machine call node at fixed frames inside `W`, closed under `K` when
`KC`, with a memory postcondition** (`call_nd_FWK` over segments with
frames; `call_ndS` with no source call): the callee runs at the caller's
frames `fs` (e.g. a user function called by the runtime, whose source is the
caller's own), its specification a segment at `fs` with `call_nd_FWK`'s
regions and frame conditions. -/
theorem call_nd_FWKS {KC : Prop} {W : FragS isa} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {nC : ND} {γ : Type _} {κ' : Sort _} {e0 lo' hi' : Int} {Ne : γ → ND} {Ex : γ → κ' → ND}
    {fs : List TermRun.Frame}
    (hR : R.OK) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp - e0 + lo') (hlo0 : lo' ≤ 0) (hkb : nC.o.sp - e0 < R.hi)
    (hhi : nC.o.sp - e0 + hi' ≤ R.hi) (hk8 : (nC.o.sp - e0) % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hFK : KC → KStable K F)
    (hKR : KC → ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hF₂ : ∀ m, F m → M m → F₂ m)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ lo' →
      hi' ≤ R'.hi → FStable R' F' → (KC → KStable K F') → (∀ m, F' m → F m) → R' = R.callee (nC.o.sp - e0) lo' hi' →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - (nC.o.sp - e0)) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) → ∀ g,
        (∃ σC c, nC.J σC c ∧ (Ne g).J (enter (nC.o.sp - e0) σC) c) →
        (∀ m, F' m → ∃ mC σC c, Abs R nC.o mC σC ∧ nC.J σC c ∧ (Ne g).J (enter (nC.o.sp - e0) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - (nC.o.sp - e0)) → Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegWS W K p lbl ms ((At exe endPc R' F' (Ne g)).at fs)
          (Frag.at (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c ∧ M s.st.1) fs))
    (hNe : ∀ g, (Ne g).o = ⟨e0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter (nC.o.sp - e0) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter (nC.o.sp - e0) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.zmms = σx.zmms → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp - e0 + (Ex g x).o.sp, []⟩, σR⟩ c') :
    SegWS W K p lbl ms ((At exe endPc R F nC).at fs) ((Next exe endPc R F₂ N E).at fs) := by
  let kc := nC.o.sp - e0
  let R' := R.callee kc lo' hi'
  have hR' : R'.OK := Region.callee_ok hR hlo hlo0 hkb hhi
  have hFR' : FStable R' F := FStable.callee hR hlo hlo0 hkb hhi hF
  let Kept : MachineData → MachineData → Prop := fun m0 m =>
    ∀ k, R.Off k → ¬ R'.Off (k - kc) → Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt m0.dmem (R.addr k) 8
  let F' : MachineData × AS × Ctl × γ → MachineData → Prop := fun G m =>
    F m ∧ Kept G.1 m ∧ Abs R nC.o G.1 G.2.1 ∧ nC.J G.2.1 G.2.2.1 ∧ (Ne G.2.2.2).J (enter kc G.2.1) G.2.2.1
  have hF' : ∀ G, FStable R' (F' G) := fun G m m' hm hd =>
    ⟨hFR' m m' hm.1 hd, fun k hk hn =>
      (hd _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkb hk8 hl8 hh8 hk hn)).trans
        (hm.2.1 k hk hn), hm.2.2⟩
  have hK' : KC → ∀ G, KStable K (F' G) := fun hc G s s' hk hm =>
    ⟨hFK hc s s' hk hm.1, fun k hk' hn => (hKR hc s s' hk hm.1 k hk' hn).trans (hm.2.1 k hk' hn), hm.2.2⟩
  refine SegWS.mono_pre (P := fun s c fs' => ∃ G, (At exe endPc R' (F' G) (Ne G.2.2.2)).at fs s c fs')
    (SegWS.exists_pre fun G => ?_) ?_
  · by_cases hG : nC.J G.2.1 G.2.2.1 ∧ (Ne G.2.2.2).J (enter kc G.2.1) G.2.2.1
    · refine (hcallee R' (F' G) hR' (Int.le_refl _) (Int.le_refl _) (hF' G) (fun hc => hK' hc G) (fun _ h => h.1)
        rfl (fun m hm k hk hn => by
          obtain ⟨j, hj, -⟩ := hm.2.2.1.slot k hk
          rw [hm.2.1 k hk hn, hj]; rfl) G.2.2.2 ⟨G.2.1, G.2.2.1, hG⟩
        (fun m hm => ⟨G.1, G.2.1, G.2.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2, hm.2.1⟩)).mono_post ?_
      rintro s c fs' ⟨⟨x, ⟨he, hn, hdc, hpc, σx, hAx, ⟨hD, hDF, hAC, hJC, hJE⟩, hJx⟩, hM⟩, rfl⟩
      obtain ⟨mC, σC, cC, g⟩ := G
      simp only at hDF hAC hJC hJE hJx hAx hpc
      have hAR : Abs R ⟨kc + (Ex g x).o.sp, []⟩ s.st.1 (leave R' kc σC σx) := by
        refine ⟨hAx.regs, hAx.zmms, hAx.status, ?_, fun k hk => ?_⟩
        · intro r k' hr
          obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
          have := hAx.so .rsp (Ex g x).o.sp (by simp [SO.get])
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
      have hL := hret g x σC cC σx c (leave R' kc σC σx) hJC hJE hJx rfl rfl rfl
        (fun k _ hn => by simp only [leave]; exact ite_eq_right hn)
      have hs : s = { s with st := (s.st.1, (Ex g x).pc) } := by rw [← hpc]; rfl
      refine ⟨?_, rfl⟩
      rw [hs]
      rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
      · exact .inl ⟨j, hj.at he hn hdc hAR (hF₂ _ hD hM)⟩
      · exact .inr ⟨y, hy.at he hn hdc hAR (hF₂ _ hD hM)⟩
    · exact SegWS.empty fun s c fs' ⟨⟨_, _, _, _, _, _, ⟨_, _, _, hJC, hJE⟩, _⟩, _⟩ => hG ⟨hJC, hJE⟩
  · rintro s c fs' ⟨⟨he, hn, hdc, hpc, σC, hA, hD, hJ⟩, rfl⟩
    obtain ⟨g, hgpc, hgJ⟩ := hent σC c hJ
    refine ⟨(s.st.1, σC, c, g), ⟨he, hn, hdc, by rw [hpc, hgpc], enter kc σC, ?_,
      ⟨hD, fun _ _ _ => rfl, hA, hJ, hgJ⟩, hgJ⟩, rfl⟩
    rw [hNe]
    refine ⟨hA.regs, hA.zmms, hA.status, ?_, fun k hk => ?_⟩
    · intro r k' hr
      obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
      have := hA.so .rsp nC.o.sp (by simp [SO.get])
      simp only [enter] at this ⊢
      rw [this, Region.callee_addr]; congr 1; omega
    · obtain ⟨j, hj, hv⟩ := hA.slot _ (Region.callee_off hlo hhi hk8 hk)
      exact ⟨j, by rw [Region.callee_addr]; exact hj, hv⟩

end Fn

end Spike.Lib.X64.Flow
