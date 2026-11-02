/-
**A runtime call inside a frame-aware fragment, landing in `X`, on x86-64** (hello.w): `X64CallS.call_nd_FWKS`'s
machine call over `Spike/Lib/HelloSegTCSX.lean`'s `SegTCSX`, so the thread worker's call of `wc_worker` is one
`SegTCSX` segment, every landing pair in the landing fragment `X`.

A runtime call pushes no source frame (its callee's entry is the caller's pair, unlike `call_ndTCSX`), so no
`X` premise at the call node is needed: the callee's segment puts its entry in `S` and `X`.

- `call_ndTSSX`: the call node, a `SegTCSX` segment at `fs` to the caller's nodes, given the callee's
  `SegTCSX` segment at `fs`.

## Differences from the AArch64 version

`Spike/Lib/A64HelloCallTSSX.lean`.

- The machine side is `X64CallS.call_nd_FWKS`'s: the callee's frame at `nC.o.sp - e0` (`hNe` at `⟨e0, []⟩`;
  x86-64's `call` pushes the return address), the bounds `hkb`/`hhi`/`hk8` in place of AArch64's 16-byte
  alignment premises (`hal`, `hk16`, `hhi0`), and the return's vector registers kept (`σR.zmms = σx.zmms`).
- The caller's cells outside the callee's region are carried as `call_nd_FWKS`'s `Kept` (their loads), not as
  `DFrame`.
- It is stated directly: there is no x86-64 `call_ndTSS` (that A64 module is not in the live closure).
-/
import Spike.Lib.X64CallS
import Spike.Lib.HelloSegTCSX

namespace Spike.Lib.X64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.HelloSegTCSX (SegTCSX)

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A runtime call node inside `S` at frames `fs`, landing in `X`** (`call_nd_FWKS` over `SegTCSX`): the
callee's specification is a `SegTCSX` segment at `fs` from its entry to its exits; its exits land at the
caller's nodes (`hret`). -/
theorem call_ndTSSX {S X : FragS isa} {nC : ND} {γ : Type _} {κ' : Sort _} {e0 lo' hi' : Int} {Ne : γ → ND}
    {Ex : γ → κ' → ND} {fs : List TermRun.Frame}
    (hR : R.OK) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp - e0 + lo') (hlo0 : lo' ≤ 0) (hkb : nC.o.sp - e0 < R.hi)
    (hhi : nC.o.sp - e0 + hi' ≤ R.hi) (hk8 : (nC.o.sp - e0) % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ lo' →
      hi' ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ g,
        SegTCSX S X p lbl ms ((At exe endPc R' F' (Ne g)).at fs)
          (Frag.at (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c) fs))
    (hNe : ∀ g, (Ne g).o = ⟨e0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter (nC.o.sp - e0) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter (nC.o.sp - e0) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.zmms = σx.zmms → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp - e0 + (Ex g x).o.sp, []⟩, σR⟩ c') :
    SegTCSX S X p lbl ms ((At exe endPc R F nC).at fs) ((Next exe endPc R F N E).at fs) := by
  -- the callee's region and its ghost-indexed frame condition
  let kc := nC.o.sp - e0
  let R' := R.callee kc lo' hi'
  have hR' : R'.OK := Region.callee_ok hR hlo hlo0 hkb hhi
  have hFR' : FStable R' F := FStable.callee hR hlo hlo0 hkb hhi hF
  let Kept : MachineData → MachineData → Prop := fun m0 m =>
    ∀ k, R.Off k → ¬ R'.Off (k - kc) → Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt m0.dmem (R.addr k) 8
  -- the ghost: the machine data and abstract state at the call, the caller's control, the callee's
  -- parameters; the facts about it ride in the frame condition (constant, so stable)
  let F' : MachineData × AS × Ctl × γ → MachineData → Prop := fun G m =>
    F m ∧ Kept G.1 m ∧ Abs R nC.o G.1 G.2.1 ∧ nC.J G.2.1 G.2.2.1 ∧ (Ne G.2.2.2).J (enter kc G.2.1) G.2.2.1
  have hF' : ∀ G, FStable R' (F' G) := fun G m m' hm hd =>
    ⟨hFR' m m' hm.1 hd, fun k hk hn =>
      (hd _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkb hk8 hl8 hh8 hk hn)).trans
        (hm.2.1 k hk hn), hm.2.2⟩
  refine SegTCSX.mono_pre (P := fun s c fs' => ∃ G, (At exe endPc R' (F' G) (Ne G.2.2.2)).at fs s c fs')
    (SegTCSX.exists_pre fun G => ?_) ?_
  · -- the callee's segment, its exits landing at the caller's nodes
    refine (hcallee R' (F' G) hR' (Int.le_refl _) (Int.le_refl _) (hF' G) (fun _ h => h.1)
      G.2.2.2).mono_post ?_
    rintro s c fs' ⟨⟨x, he, hn, hdc, hpc, σx, hAx, ⟨hD, hDF, hAC, hJC, hJE⟩, hJx⟩, rfl⟩
    refine ⟨?_, rfl⟩
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
    rw [hs]
    rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
    · exact .inl ⟨j, hj.at he hn hdc hAR hD⟩
    · exact .inr ⟨y, hy.at he hn hdc hAR hD⟩
  · -- the caller's state at the call, seen from the callee
    rintro s c fs' ⟨⟨he, hn, hdc, hpc, σC, hA, hD, hJ⟩, rfl⟩
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

/-- info: 'Spike.Lib.X64.Flow.call_ndTSSX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.call_ndTSSX
