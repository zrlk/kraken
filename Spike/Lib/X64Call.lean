/-
**Calls on x64**: a callee's whole-function `Seg` as a given node of its
caller (`call_nd`), as on AArch64 (`Spike/Lib/A64Call.lean`).

At the call node `nC` the `call` has pushed the return address: `%rsp` is
at the caller's static offset `nC.o.sp` and the pc is the callee's entry.
The callee's specification is stated over a region whose entry offsets are
`⟨e0, []⟩` (`e0 = 8` for scc's functions: the return address is the cell
`[8, 16)`), so the callee's region is `R.callee kb lo' hi'` with
`kb = nC.o.sp - e0`; it lies inside the caller's (`R.lo ≤ kb + lo'`,
`kb + hi' ≤ R.hi`), the return address cell being a cell of both. The frame
condition, the entry and return obligations are those of AArch64, with the
vector registers carried like the general ones. `call_nd_FW` is the node
over `SegW W K`, with AArch64's hypotheses (`hFK`, `hKR`, `hF₂`, a `KStable`
callee, exits with a memory postcondition).
-/
import Spike.Lib.X64Cfg

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64

/-! ## The callee's region -/

section Callee

variable {R : Region} {kc lo' hi' : Int}

/-- **A write inside the callee's region is a write inside the caller's**:
a frame condition of the caller is one of the callee. -/
theorem FStable.callee (hR : R.OK) (hlo : R.lo ≤ kc + lo') (hlo0 : lo' ≤ 0) (hkc : kc < R.hi) (hhi : kc + hi' ≤ R.hi)
    {F : MachineData → Prop} (hF : FStable R F) : FStable (R.callee kc lo' hi') F := by
  intro m m' hm hd
  refine hF m m' hm fun a ha hout => hd a ha ?_
  have hb := Region.callee_base (hi' := hi') hR hlo hlo0 hkc
  simp only [Region.callee] at hb ⊢
  omega

end Callee

/-! ## The abstract states at the callee's entry and after its return -/

/-- **The caller's abstract state seen from the callee's region**: the
same registers and flags, the cells shifted by `kb`. -/
def enter (kb : Int) (σ : AS) : AS := { σ with slot := fun k => σ.slot (kb + k) }

open Classical in
/-- The caller's abstract state after the callee returns: the callee's
registers and flags, the callee's cells inside its region, the caller's
outside. -/
noncomputable def leave (R' : Region) (kb : Int) (σC σx : AS) : AS :=
  { regs := σx.regs, zmms := σx.zmms, status := σx.status,
    slot := fun k => if R'.Off (k - kb) then σx.slot (k - kb) else σC.slot k }

/-- The only known offset of `⟨e, []⟩` is `%rsp`'s. -/
theorem SO.get_sp_only {e : Int} {r : Reg64} {k : Int} (h : SO.get ⟨e, []⟩ r = some k) : r = .rsp ∧ k = e := by
  unfold SO.get at h
  split at h
  · rename_i hr; cases h; exact ⟨hr, rfl⟩
  · cases h

/-! ## A call node -/

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A call node**: the callee's specification (`hcallee`, for every region
holding its frame `[lo', hi')` and every frame condition, entry offsets
`⟨e0, []⟩`) is a given node of the caller, from the call node `nC` (the
return address pushed) to the caller's nodes. -/
theorem call_nd {nC : ND} {γ : Type _} {κ' : Sort _} {e0 lo' hi' : Int} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hR : R.OK) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp - e0 + lo') (hlo0 : lo' ≤ 0) (hkb : nC.o.sp - e0 < R.hi)
    (hhi : nC.o.sp - e0 + hi' ≤ R.hi) (hk8 : (nC.o.sp - e0) % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ lo' → hi' ≤ R'.hi → FStable R' F' →
      ∀ g, Seg p lbl ms (At exe endPc R' F' (Ne g)) (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c))
    (hNe : ∀ g, (Ne g).o = ⟨e0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter (nC.o.sp - e0) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter (nC.o.sp - e0) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.zmms = σx.zmms → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp - e0 + (Ex g x).o.sp, []⟩, σR⟩ c') :
    Seg p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) := by
  -- the callee's region and its ghost-indexed frame condition
  let kb := nC.o.sp - e0
  let R' := R.callee kb lo' hi'
  have hR' : R'.OK := Region.callee_ok hR hlo hlo0 hkb hhi
  have hFR' : FStable R' F := FStable.callee hR hlo hlo0 hkb hhi hF
  -- the ghost: the machine data and abstract state at the call, the caller's control, the callee's
  -- parameters; the facts about it ride in the frame condition (constant, so stable)
  let F' : MachineData × AS × Ctl × γ → MachineData → Prop := fun G m =>
    F m ∧ DFrame R' G.1 m ∧ Abs R nC.o G.1 G.2.1 ∧ nC.J G.2.1 G.2.2.1 ∧ (Ne G.2.2.2).J (enter kb G.2.1) G.2.2.1
  have hF' : ∀ G, FStable R' (F' G) := fun G m m' hm hd =>
    ⟨hFR' m m' hm.1 hd, hm.2.1.trans hd, hm.2.2⟩
  refine Seg.mono_pre (P := fun s c => ∃ G, At exe endPc R' (F' G) (Ne G.2.2.2) s c)
    (Seg.exists_pre fun G => ?_) ?_
  · -- the callee's segment, its exits landing at the caller's nodes
    refine (hcallee R' (F' G) hR' (Int.le_refl _) (Int.le_refl _) (hF' G) G.2.2.2).mono_post ?_
    rintro s c ⟨x, he, hn, hdc, hpc, σx, hAx, ⟨hD, hDF, hAC, hJC, hJE⟩, hJx⟩
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
          · rw [hDF _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkb hk8 hl8 hh8 hk hin)]
            exact hj
          · simp only [leave]; rw [ite_eq_right hin]; exact hv
    have hL := hret g x σC cC σx c (leave R' kb σC σx) hJC hJE hJx rfl rfl rfl
      (fun k _ hn => by simp only [leave]; exact ite_eq_right hn)
    have hs : s = { s with st := (s.st.1, (Ex g x).pc) } := by rw [← hpc]; rfl
    rw [hs]
    rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
    · exact .inl ⟨j, hj.at he hn hdc hAR hD⟩
    · exact .inr ⟨y, hy.at he hn hdc hAR hD⟩
  · -- the caller's state at the call, seen from the callee
    rintro s c ⟨he, hn, hdc, hpc, σC, hA, hD, hJ⟩
    obtain ⟨g, hgpc, hgJ⟩ := hent σC c hJ
    refine ⟨(s.st.1, σC, c, g), he, hn, hdc, by rw [hpc, hgpc], enter kb σC, ?_,
      ⟨hD, DFrame.refl _ _, hA, hJ, hgJ⟩, hgJ⟩
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
/-- **A call node inside `W`, closed under `K` when `KC`, with a memory
postcondition**: `call_nd`, as a `SegW W K` node. The callee's
specification is required only for frame conditions that imply the
caller's `F` and that no write inside the callee's region (`FStable`)
breaks, and only at the callee's region at the call (so that a callee's
facts about its own cells may come from the caller's), with the caller's
cells outside it holding values (as at the call) and, in every state,
the call's ghost facts and those cells as in a caller's state at the
node, and its exits carry a
memory postcondition `M`: the caller lands at its nodes with any frame
condition `F₂` that `F` and `M` give (`hF₂`). The callee's frame
condition is "the caller's `F`, the caller's cells outside the callee's
region as at the call, and the call's ghost facts"; an outside move keeps
it when it keeps `F` (`hFK`) and the caller's cells (`hKR`). The callee is
promised that only under `KC`, and only then are `hFK`, `hKR` asked
(`KC := False` for a callee with no outside move in it). -/
theorem call_nd_FWK {KC : Prop} {W : Frag isa} {K : State → State → Prop} {M F₂ : MachineData → Prop}
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
        SegW W K p lbl ms (At exe endPc R' F' (Ne g))
          (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c ∧ M s.st.1))
    (hNe : ∀ g, (Ne g).o = ⟨e0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter (nC.o.sp - e0) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter (nC.o.sp - e0) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.zmms = σx.zmms → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp - e0 + (Ex g x).o.sp, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R F nC) (Next exe endPc R F₂ N E) := by
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
  refine SegW.mono_pre (P := fun s c => ∃ G, At exe endPc R' (F' G) (Ne G.2.2.2) s c)
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
    · exact SegW.empty fun s c ⟨_, _, _, _, _, _, ⟨_, _, _, hJC, hJE⟩, _⟩ => hG ⟨hJC, hJE⟩
  · rintro s c ⟨he, hn, hdc, hpc, σC, hA, hD, hJ⟩
    obtain ⟨g, hgpc, hgJ⟩ := hent σC c hJ
    refine ⟨(s.st.1, σC, c, g), he, hn, hdc, by rw [hpc, hgpc], enter kb σC, ?_,
      ⟨hD, fun _ _ _ => rfl, hA, hJ, hgJ⟩, hgJ⟩
    rw [hNe]
    refine ⟨hA.regs, hA.zmms, hA.status, ?_, fun k hk => ?_⟩
    · intro r k' hr
      obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
      have := hA.so .rsp nC.o.sp (by simp [SO.get])
      simp only [enter] at this ⊢
      rw [this, Region.callee_addr]; congr 1; omega
    · obtain ⟨j, hj, hv⟩ := hA.slot _ (Region.callee_off hlo hhi hk8 hk)
      exact ⟨j, by rw [Region.callee_addr]; exact hj, hv⟩

/-- **A call node inside `W`, closed under `K`, with a memory postcondition**
(`call_nd_FWK` with `KC := True`): `call_nd`, as a `SegW W K` node. The
callee's specification is required only for frame conditions that imply
the caller's `F` and that neither a write inside the callee's region
(`FStable`) nor an outside move (`KStable`) breaks, and only at the
callee's region at the call (so that a callee's facts about its own cells
may come from the caller's), with the caller's cells outside it holding
values (as at the call), and its exits carry a memory postcondition `M`:
the caller lands at its nodes with any frame condition `F₂` that `F` and
`M` give (`hF₂`). The callee's frame condition is "the caller's `F`, the
caller's cells outside the callee's region as at the call, and the call's
ghost facts"; an outside move keeps it when it keeps `F` (`hFK`) and the
caller's cells (`hKR`). -/
theorem call_nd_FW {W : Frag isa} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {nC : ND} {γ : Type _} {κ' : Sort _} {e0 lo' hi' : Int} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hR : R.OK) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp - e0 + lo') (hlo0 : lo' ≤ 0) (hkb : nC.o.sp - e0 < R.hi)
    (hhi : nC.o.sp - e0 + hi' ≤ R.hi) (hk8 : (nC.o.sp - e0) % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k →
      ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hF₂ : ∀ m, F m → M m → F₂ m)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ lo' → hi' ≤ R'.hi → FStable R' F' →
      KStable K F' → (∀ m, F' m → F m) → R' = R.callee (nC.o.sp - e0) lo' hi' →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - (nC.o.sp - e0)) →
        (Mem.loadInt m.dmem (R.addr k) 8).isSome) → ∀ g,
        (∃ σC c, nC.J σC c ∧ (Ne g).J (enter (nC.o.sp - e0) σC) c) →
        (∀ m, F' m → ∃ mC σC c, Abs R nC.o mC σC ∧ nC.J σC c ∧ (Ne g).J (enter (nC.o.sp - e0) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - (nC.o.sp - e0)) →
            Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW W K p lbl ms (At exe endPc R' F' (Ne g))
          (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c ∧ M s.st.1))
    (hNe : ∀ g, (Ne g).o = ⟨e0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter (nC.o.sp - e0) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter (nC.o.sp - e0) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.zmms = σx.zmms → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp - e0 + (Ex g x).o.sp, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R F nC) (Next exe endPc R F₂ N E) :=
  call_nd_FWK (KC := True) hR hF hlo hlo0 hkb hhi hk8 hl8 hh8 (fun _ => hFK) (fun _ => hKR) hF₂
    (fun R' F' h1 h2 h3 h4 h5 h6 h7 h8 h9 => hcallee R' F' h1 h2 h3 h4 (h5 trivial) h6 h7 h8 h9) hNe hent hret

/-- **A call node whose callee may use the caller's frame condition**:
`call_nd`, with the callee's specification required only for frame
conditions that imply the caller's `F` (`∀ m, F' m → F m`). A callee that touches a
runtime word outside every frame needs it: that the word is not
thread-private memory is a fact of the caller's `F`. (`call_nd_FW` with no
predicate, no outside moves and no postcondition.) -/
theorem call_nd_F {nC : ND} {γ : Type _} {κ' : Sort _} {e0 lo' hi' : Int} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hR : R.OK) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp - e0 + lo') (hlo0 : lo' ≤ 0) (hkb : nC.o.sp - e0 < R.hi)
    (hhi : nC.o.sp - e0 + hi' ≤ R.hi) (hk8 : (nC.o.sp - e0) % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ lo' → hi' ≤ R'.hi → FStable R' F' →
      (∀ m, F' m → F m) → ∀ g,
        Seg p lbl ms (At exe endPc R' F' (Ne g)) (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c))
    (hNe : ∀ g, (Ne g).o = ⟨e0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter (nC.o.sp - e0) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter (nC.o.sp - e0) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.zmms = σx.zmms → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (nC.o.sp - e0) lo' hi').Off (k - (nC.o.sp - e0)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp - e0 + (Ex g x).o.sp, []⟩, σR⟩ c') :
    Seg p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) :=
  (call_nd_FW (W := fun _ _ => True) (K := fun _ _ => False) (M := fun _ => True) hR hF hlo hlo0 hkb hhi
    hk8 hl8 hh8 (KStable.none F) (fun _ _ h => h.elim) (fun _ h _ => h)
    (fun R' F' h1 h3 h4 h5 _ h6 _ _ g _ _ =>
      (SegW.ofSeg (hcallee R' F' h1 h3 h4 h5 h6 g)).mono_post fun _ _ ⟨x, h⟩ => ⟨x, h, trivial⟩)
    hNe hent hret).toSeg

/-! ## Entering and leaving a callee's region

`call_nd_FWK`'s two halves as facts about one state, for a segment that
crosses a call without returning inside it (an allocation's continuation
lands in the callee), as on AArch64. -/

/-- **The caller's cells outside the callee's region** (at `kb`, from `lo'`
to `hi'`) are as in `m0`. -/
def CKept (R : Region) (kb lo' hi' : Int) (m0 m : MachineData) : Prop :=
  ∀ k, R.Off k → ¬ (R.callee kb lo' hi').Off (k - kb) →
    Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt m0.dmem (R.addr k) 8

/-- **The callee's frame condition at a call** from the caller's state
`m0`, `σC` at offsets `o` (the callee's region at `kb`): the caller's `F`,
its cells outside the callee's region as in `m0`, and `m0`, `σC` the
caller's. No write inside the callee's region breaks it. -/
theorem fstable_enter {kb lo' hi' : Int} {o : SO} {m0 : MachineData} {σC : AS}
    (hR : R.OK) (hF : FStable R F) (hlo : R.lo ≤ kb + lo') (hlo0 : lo' ≤ 0) (hkb : kb < R.hi)
    (hhi : kb + hi' ≤ R.hi) (hk8 : kb % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0) :
    FStable (R.callee kb lo' hi') (fun m => F m ∧ CKept R kb lo' hi' m0 m ∧ Abs R o m0 σC) := fun m m' hm hd =>
  ⟨FStable.callee hR hlo hlo0 hkb hhi hF m m' hm.1 hd, fun k hk hn =>
    (hd _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkb hk8 hl8 hh8 hk hn)).trans (hm.2.1 k hk hn), hm.2.2⟩

/-- **Entering the callee's region**: a state at the call node `nC` (the
return address pushed) is at the callee's entry (offsets `⟨e0, []⟩`) in the
callee's region at `kb = nC.o.sp - e0`, under the callee's frame condition
from it (`fstable_enter`), the abstract state the caller's entered. -/
theorem at_enter {nC : ND} {e0 lo' hi' : Int} (hlo : R.lo ≤ nC.o.sp - e0 + lo')
    (hhi : nC.o.sp - e0 + hi' ≤ R.hi) (hk8 : (nC.o.sp - e0) % 8 = 0) {s : State} {c : Ctl}
    (h : At exe endPc R F nC s c) :
    ∃ m0 σC, At exe endPc (R.callee (nC.o.sp - e0) lo' hi')
      (fun m => F m ∧ CKept R (nC.o.sp - e0) lo' hi' m0 m ∧ Abs R nC.o m0 σC)
      ⟨nC.pc, ⟨e0, []⟩, fun σ c' => c' = c ∧ σ = enter (nC.o.sp - e0) σC ∧ nC.J σC c⟩ s c := by
  obtain ⟨he, hn, hdc, hpc, σC, hA, hD, hJ⟩ := h
  refine ⟨s.st.1, σC, he, hn, hdc, hpc, enter (nC.o.sp - e0) σC,
    ⟨hA.regs, hA.zmms, hA.status, ?_, fun k hk => ?_⟩, ⟨hD, fun _ _ _ => rfl, hA⟩, rfl, rfl, hJ⟩
  · intro r k' hr
    obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
    have := hA.so .rsp nC.o.sp (by simp [SO.get])
    simp only [enter] at this ⊢
    rw [this, Region.callee_addr]; congr 1; omega
  · obtain ⟨j, hj, hv⟩ := hA.slot _ (Region.callee_off hlo hhi hk8 hk)
    exact ⟨j, by rw [Region.callee_addr]; exact hj, hv⟩

/-- **Leaving the callee's region**: a state at a node `x` of the callee
(offsets `⟨e, []⟩`), under a frame condition giving the caller's `F`, its
cells outside the callee's region as in a caller's state `m0`, `σC` of `P`,
is at `x`'s pc in the caller's region (`%rsp` at `kb + e`), the abstract
state the caller's left (`leave`). -/
theorem at_leave {kb lo' hi' e : Int} {F' : MachineData → Prop} {P : AS → Prop} {x : ND} (hx : x.o = ⟨e, []⟩)
    (hF' : ∀ m, F' m → F m ∧ ∃ m0 σC o, CKept R kb lo' hi' m0 m ∧ Abs R o m0 σC ∧ P σC)
    {s : State} {c : Ctl} (h : At exe endPc (R.callee kb lo' hi') F' x s c) :
    At exe endPc R F ⟨x.pc, ⟨kb + e, []⟩, fun σ c => ∃ σx σC, x.J σx c ∧ P σC ∧
      σ = leave (R.callee kb lo' hi') kb σC σx⟩ s c := by
  obtain ⟨he, hn, hdc, hpc, σx, hAx, hD, hJx⟩ := h
  obtain ⟨hDF, m0, σC, o, hK, hAC, hP⟩ := hF' _ hD
  refine ⟨he, hn, hdc, hpc, leave (R.callee kb lo' hi') kb σC σx,
    ⟨hAx.regs, hAx.zmms, hAx.status, ?_, fun k hk => ?_⟩, hDF, σx, σC, hJx, hP, rfl⟩
  · intro r k' hr
    obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
    have := hAx.so .rsp e (by rw [hx]; simp [SO.get])
    simp only [leave] at this ⊢
    rw [this, Region.callee_addr]
  · by_cases hin : (R.callee kb lo' hi').Off (k - kb)
    · obtain ⟨j, hj, hv⟩ := hAx.slot _ hin
      refine ⟨j, ?_, ?_⟩
      · rw [Region.callee_addr, show kb + (k - kb) = k by omega] at hj; exact hj
      · simp only [leave]; rw [ite_eq_left hin]; exact hv
    · obtain ⟨j, hj, hv⟩ := hAC.slot k hk
      refine ⟨j, ?_, ?_⟩
      · rw [hK k hk hin]; exact hj
      · simp only [leave]; rw [ite_eq_right hin]; exact hv

end Fn

end Spike.Lib.X64
