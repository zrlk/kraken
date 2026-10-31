/-
**A call node whose callee is promised an entry-only fact** (x86-64, the
twin of `Spike/Lib/A64Call.lean`'s `call_nd_FWP`): `call_nd_FWK` with the
caller at the frame `F ∧ P`, the callee's specification allowed to assume
`P` of the memory at its entry.

- `call_nd_FWP`: the node.
-/
import Spike.Lib.X64Call

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

open Classical in
/-- **A call node whose callee is also promised an entry-only fact `P`**:
`call_nd_FWK` with the caller at frame `F ∧ P`, where the callee's
specification may assume `P` of the memory at its entry (the caller's memory
at the call, unchanged by the call itself). `P` need not be stable: it is not
part of the callee's frame condition, and nothing about it is claimed after
the return (the caller lands with `F₂` from `F` and `M` alone). -/
theorem call_nd_FWP {KC : Prop} {W : Frag isa} {K : State → State → Prop} {M F₂ P : MachineData → Prop}
    {nC : ND} {γ : Type _} {κ' : Sort _} {e0 lo' hi' : Int} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hR : R.OK) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp - e0 + lo') (hlo0 : lo' ≤ 0) (hkb : nC.o.sp - e0 < R.hi)
    (hhi : nC.o.sp - e0 + hi' ≤ R.hi) (hk8 : (nC.o.sp - e0) % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hFK : KC → KStable K F)
    (hKR : KC → ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k →
      ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hF₂ : ∀ m, F m → M m → F₂ m)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ lo' → hi' ≤ R'.hi → FStable R' F' →
      (KC → KStable K F') → (∀ m, F' m → F m) → R' = R.callee (nC.o.sp - e0) lo' hi' →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - (nC.o.sp - e0)) →
        (Mem.loadInt m.dmem (R.addr k) 8).isSome) → ∀ g,
        (∃ σC c, nC.J σC c ∧ (Ne g).J (enter (nC.o.sp - e0) σC) c) →
        (∀ m, F' m → ∃ mC σC c, Abs R nC.o mC σC ∧ nC.J σC c ∧ (Ne g).J (enter (nC.o.sp - e0) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - (nC.o.sp - e0)) →
            Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW W K p lbl ms (fun s c => At exe endPc R' F' (Ne g) s c ∧ P s.st.1)
          (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c ∧ M s.st.1))
    (hNe : ∀ g, (Ne g).o = ⟨e0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter (nC.o.sp - e0) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter (nC.o.sp - e0) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.zmms = σx.zmms → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp - e0 + (Ex g x).o.sp, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R (fun m => F m ∧ P m) nC) (Next exe endPc R F₂ N E) := by
  let kb := nC.o.sp - e0
  let R' := R.callee kb lo' hi'
  have hR' : R'.OK := Region.callee_ok hR hlo hlo0 hkb hhi
  have hFR' : FStable R' F := FStable.callee hR hlo hlo0 hkb hhi hF
  -- the caller's cells outside the callee's region, as in `m0`
  let Kept : MachineData → MachineData → Prop := fun m0 m =>
    ∀ k, R.Off k → ¬ R'.Off (k - kb) → Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt m0.dmem (R.addr k) 8
  let F' : MachineData × AS × Ctl × γ → MachineData → Prop := fun G m =>
    F m ∧ Kept G.1 m ∧ Abs R nC.o G.1 G.2.1 ∧ nC.J G.2.1 G.2.2.1 ∧ (Ne G.2.2.2).J (enter kb G.2.1) G.2.2.1
  have hF' : ∀ G, FStable R' (F' G) := fun G m m' hm hd =>
    ⟨hFR' m m' hm.1 hd, fun k hk hn =>
      (hd _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkb hk8 hl8 hh8 hk hn)).trans
        (hm.2.1 k hk hn), hm.2.2⟩
  have hK' : KC → ∀ G, KStable K (F' G) := fun hc G s s' hk hm =>
    ⟨hFK hc s s' hk hm.1, fun k hk' hn => (hKR hc s s' hk hm.1 k hk' hn).trans (hm.2.1 k hk' hn), hm.2.2⟩
  refine SegW.mono_pre (P := fun s c => ∃ G, At exe endPc R' (F' G) (Ne G.2.2.2) s c ∧ P s.st.1)
    (SegW.exists_pre fun G => ?_) ?_
  · by_cases hG : nC.J G.2.1 G.2.2.1 ∧ (Ne G.2.2.2).J (enter kb G.2.1) G.2.2.1
    · refine (hcallee R' (F' G) hR' (Int.le_refl _) (Int.le_refl _) (hF' G) (fun hc => hK' hc G)
        (fun _ h => h.1) rfl (fun m hm k hk hn => by
          obtain ⟨j, hj, -⟩ := hm.2.2.1.slot k hk
          rw [hm.2.1 k hk hn, hj]; rfl) G.2.2.2 ⟨G.2.1, G.2.2.1, hG⟩
        (fun m hm => ⟨G.1, G.2.1, G.2.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2, hm.2.1⟩)).mono_post ?_
      rintro s c ⟨x, ⟨he, hn, hdc, hpc, σx, hAx, ⟨hD, hDF, hAC, hJC, hJE⟩, hJx⟩, hM⟩
      obtain ⟨mC, σC, cC, g⟩ := G
      simp only at hDF hAC hJC hJE hJx hAx hpc
      have hAR : Abs R ⟨kb + (Ex g x).o.sp, []⟩ s.st.1 (leave R' kb σC σx) := by
        refine ⟨hAx.regs, hAx.zmms, hAx.status, ?_, fun k hk => ?_⟩
        · intro r k' hr
          obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
          have := hAx.so .rsp (Ex g x).o.sp (by simp [SO.get])
          simp only [leave] at this ⊢
          rw [this, Region.callee_addr]
        · by_cases hin : R'.Off (k - kb)
          · obtain ⟨j, hj, hv⟩ := hAx.slot _ hin
            refine ⟨j, ?_, ?_⟩
            · rw [Region.callee_addr, show kb + (k - kb) = k by omega] at hj; exact hj
            · simp only [leave]; rw [ite_eq_left hin]; exact hv
          · obtain ⟨j, hj, hv⟩ := hAC.slot k hk
            refine ⟨j, ?_, ?_⟩
            · rw [hDF k hk hin]
              exact hj
            · simp only [leave]; rw [ite_eq_right hin]; exact hv
      have hL := hret g x σC cC σx c (leave R' kb σC σx) hJC hJE hJx rfl rfl rfl
        (fun k _ hn => by simp only [leave]; exact ite_eq_right hn)
      have hs : s = { s with st := (s.st.1, (Ex g x).pc) } := by rw [← hpc]; rfl
      rw [hs]
      rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
      · exact .inl ⟨j, hj.at he hn hdc hAR (hF₂ _ hD hM)⟩
      · exact .inr ⟨y, hy.at he hn hdc hAR (hF₂ _ hD hM)⟩
    · exact SegW.empty fun s c ⟨⟨_, _, _, _, _, _, ⟨_, _, _, hJC, hJE⟩, _⟩, _⟩ => hG ⟨hJC, hJE⟩
  · rintro s c ⟨he, hn, hdc, hpc, σC, hA, ⟨hD, hP⟩, hJ⟩
    obtain ⟨g, hgpc, hgJ⟩ := hent σC c hJ
    refine ⟨(s.st.1, σC, c, g), ⟨he, hn, hdc, by rw [hpc, hgpc], enter kb σC, ?_,
      ⟨hD, fun _ _ _ => rfl, hA, hJ, hgJ⟩, hgJ⟩, hP⟩
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

end Spike.Lib.X64

/-- info: 'Spike.Lib.X64.call_nd_FWP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.call_nd_FWP
