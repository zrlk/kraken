/-
**A source call inside a frame-aware fragment, landing in `X`, on x86-64**:
`X64CallS.call_ndSG`'s source call over `Spike/Lib/HelloSegTCSX.lean`'s `SegTCSX` (the worker's segments at
any call depth, their invariant inside a fragment `S`, their landing pairs inside `X`), so hello's worker's
call of `print` (the frame `uFrame` pushed) is one `SegTCSX` segment at the worker's frames.

At the call node `nC` (after the caller's `call`: the pc at the callee's entry offset `e0`, the return
address pushed) the caller's source is at `let x = call f is a in e` (`CallToI`). The callee's first row
takes the source's call (`SegTCSX.pre_run`); its exits take the return (`SegTCSX.post_run`, `hret`: a frame
run from `fr :: fs` back to `fs`). The callee's specification (`hcallee`) is a `SegTCSX` segment at
`fr :: fs` from its entry to its exits, at `call_ndS`'s regions and frame conditions (no kernel closure:
`SegTCSX` has no outside move). `hWC`, `hXC`: `S` and `X` at the call node's pairs.

- `call_ndTCSX`: the call node, a `SegTCSX` segment at `fs` to the caller's nodes.

## Differences from the AArch64 version

`Spike/Lib/A64HelloCallTCSX.lean`.

- The machine side is `X64CallS.call_ndSG`'s: the callee's frame at `nC.o.sp - e0` (`hNe` at `⟨e0, []⟩`),
  the bounds `hkb`/`hhi`/`hk8` in place of AArch64's 16-byte alignment premises (`hal`, `hk16`, `hhi0`), and
  the return's vector registers kept (`σR.zmms = σx.zmms`).
- It imports `Spike/Lib/HelloSegTCSX.lean` (where `SegTCSX` lives) directly, not the AArch64 version's
  `HelloSegTCSXC`, and is stated directly rather than as a variant of a `SegTCS` call node.
-/
import Spike.Lib.X64HelloCallTCS
import Spike.Lib.HelloSegTCSX

namespace Spike.Lib.X64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.HelloSegTCSX (SegTCSX)

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

open Classical in
/-- **A source call node inside `S`, landing in `X`** (`call_ndSG` over `SegTCSX`): at the caller's frames
`fs`, from the call node `nC` (`hent`: its source control calls, `CallToI`, and the callee's entry node holds
at the callee's control) to the caller's nodes, the return taken (`hret`). The callee's specification
(`hcallee`) is a `SegTCSX` segment at the frames `fr :: fs` with `call_ndS`'s regions and frame conditions;
`hWC`, `hXC`: `S` and `X` at the call node's pairs (the callee's entry row lands from them through the
source's call). The return's frame run adds no landing pair: the callee's exits are landed by its own rows,
in `X`. -/
theorem call_ndTCSX {S X : FragS isa} {nC : ND} {γ : Type _} {κ' : Sort _} {e0 lo' hi' : Int} {Ne : γ → ND}
    {Ex : γ → κ' → ND} {fs : List TermRun.Frame}
    (hR : R.OK) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp - e0 + lo') (hlo0 : lo' ≤ 0) (hkb : nC.o.sp - e0 < R.hi)
    (hhi : nC.o.sp - e0 + hi' ≤ R.hi) (hk8 : (nC.o.sp - e0) % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hWC : ∀ s c, At exe endPc R F nC s c → S s c fs) (hXC : ∀ s c, At exe endPc R F nC s c → X s c fs)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ lo' →
      hi' ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → R' = R.callee (nC.o.sp - e0) lo' hi' →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - (nC.o.sp - e0)) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g (fr : TermRun.Frame),
        (∃ σC c cE, nC.J σC c ∧ CallToI p c cE fr ∧ (Ne g).J (enter (nC.o.sp - e0) σC) cE) →
        (∀ m, F' m → ∃ mC σC c cE, Abs R nC.o mC σC ∧ nC.J σC c ∧ CallToI p c cE fr ∧
          (Ne g).J (enter (nC.o.sp - e0) σC) cE ∧
          ∀ k, R.Off k → ¬ R'.Off (k - (nC.o.sp - e0)) →
            Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegTCSX S X p lbl ms ((At exe endPc R' F' (Ne g)).at (fr :: fs))
          (Frag.at (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c) (fr :: fs)))
    (hNe : ∀ g, (Ne g).o = ⟨e0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g cE fr, CallToI p c cE fr ∧ (Ne g).pc = nC.pc ∧
      (Ne g).J (enter (nC.o.sp - e0) σC) cE)
    (hret : ∀ g x σC c cE fr σx c' (σR : AS), nC.J σC c → CallToI p c cE fr →
      (Ne g).J (enter (nC.o.sp - e0) σC) cE →
      (Ex g x).J σx c' → σR.regs = σx.regs → σR.zmms = σx.zmms → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) → σR.slot k = σC.slot k) →
      ∃ c'', FrameRun p (c', fr :: fs) (c'', fs) ∧
        Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp - e0 + (Ex g x).o.sp, []⟩, σR⟩ c'') :
    SegTCSX S X p lbl ms ((At exe endPc R F nC).at fs) ((Next exe endPc R F N E).at fs) := by
  let kc := nC.o.sp - e0
  let R' := R.callee kc lo' hi'
  have hR' : R'.OK := Region.callee_ok hR hlo hlo0 hkb hhi
  have hFR' : FStable R' F := FStable.callee hR hlo hlo0 hkb hhi hF
  let F' := CallGFI p R F nC e0 lo' hi' Ne
  have hF' : ∀ G, FStable R' (F' G) := fun G m m' hm hd =>
    ⟨hFR' m m' hm.1 hd, fun k hk hn =>
      (hd _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkb hk8 hl8 hh8 hk hn)).trans
        (hm.2.1 k hk hn), hm.2.2⟩
  let PE : FragS isa := fun s c fs' =>
    ∃ G : MachineData × AS × Ctl × Ctl × TermRun.Frame × γ,
      (At exe endPc R' (F' G) (Ne G.2.2.2.2.2)).at (G.2.2.2.2.1 :: fs) s c fs'
  refine SegTCSX.post_run (SegTCSX.pre_run (P' := PE) (SegTCSX.exists_pre fun G => ?_)
    fun s c fs' h => ⟨?_, ?_, ?_⟩)
  · obtain ⟨mC, σC, cC, cE, fr, g⟩ := G
    by_cases hG : nC.J σC cC ∧ CallToI p cC cE fr ∧ (Ne g).J (enter kc σC) cE
    · refine (hcallee R' (F' (mC, σC, cC, cE, fr, g)) hR' (Int.le_refl _) (Int.le_refl _) (hF' _)
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

/-- info: 'Spike.Lib.X64.Flow.call_ndTCSX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.call_ndTCSX
