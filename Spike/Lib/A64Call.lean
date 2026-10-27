/-
**Calls on AArch64**: a callee's whole-function `Seg` as a given node of
its caller (`call_nd`).

A function's specification (`seg_print`, `seg_printL`, …) is stated for
every region `R'` that holds its frame and every frame condition `F'` no
write inside `R'` breaks (`FStable`). At a call the caller is at its call
node `nC`, with `sp` at the static offset `kc = nC.o.sp` of its region `R`,
the pc at the callee's entry and the return address in `x30` (the closed
form of the block ending with `bl`). The callee runs in the region
`R.callee kc lo' hi'`, based at that `sp`, with the frame condition "the
caller's `F`, and the memory outside the callee's region as at the call".
The callee's region lies inside the caller's (`R.lo ≤ kc + lo'`, `hi' ≤ 0`),
so a callee write is a write inside `R` and keeps `F`.

- **Entry** (`hent`): the caller's state, seen from the callee's region
  (`enter`: the same registers and flags, the cells shifted by `kc`), is in
  the callee's entry invariant, at the callee's entry offsets `⟨0, []⟩`.
- **Return** (`hret`): at every exit of the callee, the state seen from the
  caller's region lands at a node of the caller, with only `sp`'s offset
  known (`kc` plus the exit's). The obligation is stated for any abstract
  state with the callee's registers and flags whose cells outside the
  callee's region are the caller's at the call (`σR`): a caller cell the
  callee cannot write keeps its value.

The callee's ghost parameters (`g`: the caller's `x29`, the return address,
the source control) are chosen at the call (`hent`).
-/
import Spike.Lib.A64Cfg

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64

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

/-! ## The abstract state at the callee's entry -/

/-- **The caller's abstract state seen from the callee's region**: the
same registers and flags, the cells shifted by `kc`. -/
def enter (kc : Int) (σ : AS) : AS := { σ with slot := fun k => σ.slot (kc + k) }

/-! ## A call node -/

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

open Classical in
/-- The caller's abstract state after the callee returns: the callee's
registers and flags, the callee's cells inside its region, the caller's
outside. -/
noncomputable def leave (R' : Region) (kc : Int) (σC σx : AS) : AS :=
  { regs := σx.regs, status := σx.status, slot := fun k => if R'.Off (k - kc) then σx.slot (k - kc) else σC.slot k }

/-- **The caller's abstract state after the callee returns** (`leave`): a
callee's state `σx` in its region `R.callee kc lo' hi'` at offsets `o`, the
caller's cells outside it as in `mC`, which `σC` abstracts, give the
caller's state in `R` at the callee's `sp` shifted by `kc`. -/
theorem abs_leave {R : Region} {kc lo' hi' : Int} {o oC : SO} {m mC : MachineData} {σC σx : AS}
    (hAx : Abs (R.callee kc lo' hi') o m σx) (hAC : Abs R oC mC σC)
    (hDF : ∀ k, R.Off k → ¬ (R.callee kc lo' hi').Off (k - kc) →
      Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) :
    Abs R ⟨kc + o.sp, []⟩ m (leave (R.callee kc lo' hi') kc σC σx) := by
  refine ⟨hAx.regs, hAx.status, ?_, fun k hk => ?_⟩
  · intro r k' hr
    rcases r with y | _
    · cases hr
    · simp only [SO.get, Option.some.injEq] at hr
      subst hr
      have := hAx.so .SP _ rfl
      simp only [leave] at this ⊢
      rw [this, Region.callee_addr]
  · by_cases hin : (R.callee kc lo' hi').Off (k - kc)
    · obtain ⟨j, hj, hv⟩ := hAx.slot _ hin
      refine ⟨j, ?_, ?_⟩
      · rw [Region.callee_addr, show kc + (k - kc) = k by omega] at hj; exact hj
      · simp only [leave]; rw [ite_eq_left hin]; exact hv
    · obtain ⟨j, hj, hv⟩ := hAC.slot k hk
      refine ⟨j, ?_, ?_⟩
      · rw [hDF k hk hin]
        exact hj
      · simp only [leave]; rw [ite_eq_right hin]; exact hv

/-- **A call node**: the callee's specification (`hcallee`, for every region
holding its frame `[lo', hi')` and every frame condition) is a given node
of the caller, from the call node `nC` to the caller's nodes. -/
theorem call_nd {nC : ND} {γ : Type _} {κ' : Sort _} {lo' hi' : Int} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp + lo') (hlo0 : lo' ≤ 0) (hkc : nC.o.sp < R.hi) (hhi0 : hi' ≤ 0)
    (hk16 : nC.o.sp % 16 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ lo' →
      hi' ≤ R'.hi → FStable R' F' → ∀ g,
        Seg p lbl ms (At exe endPc R' F' (Ne g)) (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter nC.o.sp σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter nC.o.sp σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp + (Ex g x).o.sp, []⟩, σR⟩ c') :
    Seg p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) := by
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
  refine Seg.mono_pre (P := fun s c => ∃ G, At exe endPc R' (F' G) (Ne G.2.2.2) s c)
    (Seg.exists_pre fun G => ?_) ?_
  · -- the callee's segment, its exits landing at the caller's nodes
    refine (hcallee R' (F' G) hR' hal' (Int.le_refl _) (Int.le_refl _) (hF' G) G.2.2.2).mono_post ?_
    rintro s c ⟨x, he, hn, hdc, hpc, σx, hAx, ⟨hD, hDF, hAC, hJC, hJE⟩, hJx⟩
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
    rintro s c ⟨he, hn, hdc, hpc, σC, hA, hD, hJ⟩
    obtain ⟨g, hgpc, hgJ⟩ := hent σC c hJ
    refine ⟨(s.st.1, σC, c, g), he, hn, hdc, by rw [hpc, hgpc], enter kc σC, ?_,
      ⟨hD, DFrame.refl _ _, hA, hJ, hgJ⟩, hgJ⟩
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
/-- **A call node inside `W`, closed under `K` when `KC`, with a memory postcondition**:
`call_nd`, as a `SegW W K` node. The callee's specification is required only
for frame conditions that imply the caller's `F` and that neither a write
inside the callee's region (`FStable`) nor an outside move (`KStable`)
breaks, and only at the callee's region at the call (so that a callee's
facts about its own cells may come from the caller's), with the caller's
cells outside it holding values (as at the call) and, in every state,
the call's ghost facts and those cells as in a caller's state at the
node, and its exits carry
a memory postcondition `M`: the caller lands at
its nodes with any frame condition `F₂` that `F` and `M` give (`hF₂`). The
callee's frame condition is "the caller's `F`, the caller's cells outside
the callee's region as at the call, and the call's ghost facts"; an outside
move keeps it when it keeps `F` (`hFK`) and the caller's cells (`hKR`). The
callee is promised that only under `KC`, and only then are `hFK`, `hKR`
asked (`KC := False` for a callee with no outside move in it). -/
theorem call_nd_FWK {KC : Prop} {W : Frag isaLSE2} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {nC : ND} {γ : Type _} {κ' : Sort _} {lo' hi' : Int} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp + lo') (hlo0 : lo' ≤ 0) (hkc : nC.o.sp < R.hi) (hhi0 : hi' ≤ 0)
    (hk16 : nC.o.sp % 16 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hFK : KC → KStable K F)
    (hKR : KC → ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hF₂ : ∀ m, F m → M m → F₂ m)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ lo' →
      hi' ≤ R'.hi → FStable R' F' → (KC → KStable K F') → (∀ m, F' m → F m) → R' = R.callee nC.o.sp lo' hi' →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - nC.o.sp) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) → ∀ g,
        (∃ σC c, nC.J σC c ∧ (Ne g).J (enter nC.o.sp σC) c) →
        (∀ m, F' m → ∃ mC σC c, Abs R nC.o mC σC ∧ nC.J σC c ∧ (Ne g).J (enter nC.o.sp σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - nC.o.sp) → Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW W K p lbl ms (At exe endPc R' F' (Ne g))
          (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c ∧ M s.st.1))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter nC.o.sp σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter nC.o.sp σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp + (Ex g x).o.sp, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R F nC) (Next exe endPc R F₂ N E) := by
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
  let F' : MachineData × AS × Ctl × γ → MachineData → Prop := fun G m =>
    F m ∧ Kept G.1 m ∧ Abs R nC.o G.1 G.2.1 ∧ nC.J G.2.1 G.2.2.1 ∧ (Ne G.2.2.2).J (enter kc G.2.1) G.2.2.1
  have hF' : ∀ G, FStable R' (F' G) := fun G m m' hm hd =>
    ⟨hFR' m m' hm.1 hd, fun k hk hn =>
      (hd _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkc (by omega) hl8 hh8 hk hn)).trans
        (hm.2.1 k hk hn), hm.2.2⟩
  have hK' : KC → ∀ G, KStable K (F' G) := fun hc G s s' hk hm =>
    ⟨hFK hc s s' hk hm.1, fun k hk' hn => (hKR hc s s' hk hm.1 k hk' hn).trans (hm.2.1 k hk' hn), hm.2.2⟩
  refine SegW.mono_pre (P := fun s c => ∃ G, At exe endPc R' (F' G) (Ne G.2.2.2) s c)
    (SegW.exists_pre fun G => ?_) ?_
  · by_cases hG : nC.J G.2.1 G.2.2.1 ∧ (Ne G.2.2.2).J (enter kc G.2.1) G.2.2.1
    · refine (hcallee R' (F' G) hR' hal' (Int.le_refl _) (Int.le_refl _) (hF' G) (fun hc => hK' hc G) (fun _ h => h.1)
        rfl (fun m hm k hk hn => by
          obtain ⟨j, hj, -⟩ := hm.2.2.1.slot k hk
          rw [hm.2.1 k hk hn, hj]; rfl) G.2.2.2 ⟨G.2.1, G.2.2.1, hG⟩
        (fun m hm => ⟨G.1, G.2.1, G.2.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2, hm.2.1⟩)).mono_post ?_
      rintro s c ⟨x, ⟨he, hn, hdc, hpc, σx, hAx, ⟨hD, hDF, hAC, hJC, hJE⟩, hJx⟩, hM⟩
      obtain ⟨mC, σC, cC, g⟩ := G
      simp only at hDF hAC hJC hJE hJx hAx hpc
      have hAR : Abs R ⟨kc + (Ex g x).o.sp, []⟩ s.st.1 (leave R' kc σC σx) := abs_leave hAx hAC hDF
      have hL := hret g x σC cC σx c (leave R' kc σC σx) hJC hJE hJx rfl rfl
        (fun k _ hn => by simp only [leave]; exact ite_eq_right hn)
      have hs : s = { s with st := (s.st.1, (Ex g x).pc) } := by rw [← hpc]; rfl
      rw [hs]
      rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
      · exact .inl ⟨j, hj.at he hn hdc hAR (hF₂ _ hD hM)⟩
      · exact .inr ⟨y, hy.at he hn hdc hAR (hF₂ _ hD hM)⟩
    · exact SegW.empty fun s c ⟨_, _, _, _, _, _, ⟨_, _, _, hJC, hJE⟩, _⟩ => hG ⟨hJC, hJE⟩
  · rintro s c ⟨he, hn, hdc, hpc, σC, hA, hD, hJ⟩
    obtain ⟨g, hgpc, hgJ⟩ := hent σC c hJ
    refine ⟨(s.st.1, σC, c, g), he, hn, hdc, by rw [hpc, hgpc], enter kc σC, ?_,
      ⟨hD, fun _ _ _ => rfl, hA, hJ, hgJ⟩, hgJ⟩
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

/-- **A call node inside `W`, closed under `K`, with a memory postcondition**
(`call_nd_FWK` with `KC := True`):
`call_nd`, as a `SegW W K` node. The callee's specification is required only
for frame conditions that imply the caller's `F` and that neither a write
inside the callee's region (`FStable`) nor an outside move (`KStable`)
breaks, and only at the callee's region at the call (so that a callee's
facts about its own cells may come from the caller's), with the caller's
cells outside it holding values (as at the call) and, in every state,
the call's ghost facts and those cells as in a caller's state at the
node, and its exits carry
a memory postcondition `M`: the caller lands at
its nodes with any frame condition `F₂` that `F` and `M` give (`hF₂`). The
callee's frame condition is "the caller's `F`, the caller's cells outside
the callee's region as at the call, and the call's ghost facts"; an outside
move keeps it when it keeps `F` (`hFK`) and the caller's cells (`hKR`). -/
theorem call_nd_FW {W : Frag isaLSE2} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {nC : ND} {γ : Type _} {κ' : Sort _} {lo' hi' : Int} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp + lo') (hlo0 : lo' ≤ 0) (hkc : nC.o.sp < R.hi) (hhi0 : hi' ≤ 0)
    (hk16 : nC.o.sp % 16 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hF₂ : ∀ m, F m → M m → F₂ m)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ lo' →
      hi' ≤ R'.hi → FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee nC.o.sp lo' hi' →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - nC.o.sp) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) → ∀ g,
        (∃ σC c, nC.J σC c ∧ (Ne g).J (enter nC.o.sp σC) c) →
        (∀ m, F' m → ∃ mC σC c, Abs R nC.o mC σC ∧ nC.J σC c ∧ (Ne g).J (enter nC.o.sp σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - nC.o.sp) → Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW W K p lbl ms (At exe endPc R' F' (Ne g))
          (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c ∧ M s.st.1))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter nC.o.sp σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter nC.o.sp σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp + (Ex g x).o.sp, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R F nC) (Next exe endPc R F₂ N E) :=
  call_nd_FWK (KC := True) hR hal hF hlo hlo0 hkc hhi0 hk16 hl8 hh8 (fun _ => hFK) (fun _ => hKR) hF₂
    (fun R' F' h1 h2 h3 h4 h5 h6 h7 h8 h9 => hcallee R' F' h1 h2 h3 h4 h5 (h6 trivial) h7 h8 h9) hNe hent hret

/-- **A call node whose callee may use the caller's frame condition**:
`call_nd`, with the callee's specification required only for frame
conditions that imply the caller's `F` (`∀ m, F' m → F m`). A callee that touches a
runtime word outside every frame needs it: that the word is not thread-private
memory is a fact of the caller's `F`. (`call_nd_FW` with no predicate, no
outside moves and no postcondition.) -/
theorem call_nd_F {nC : ND} {γ : Type _} {κ' : Sort _} {lo' hi' : Int} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp + lo') (hlo0 : lo' ≤ 0) (hkc : nC.o.sp < R.hi) (hhi0 : hi' ≤ 0)
    (hk16 : nC.o.sp % 16 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0)
    (hcallee : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ lo' →
      hi' ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ g,
        Seg p lbl ms (At exe endPc R' F' (Ne g)) (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter nC.o.sp σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter nC.o.sp σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨nC.o.sp + (Ex g x).o.sp, []⟩, σR⟩ c') :
    Seg p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) :=
  (call_nd_FW (W := fun _ _ => True) (K := fun _ _ => False) (M := fun _ => True) hR hal hF hlo hlo0 hkc hhi0
    hk16 hl8 hh8 (KStable.none F) (fun _ _ h => h.elim) (fun _ h _ => h)
    (fun R' F' h1 h2 h3 h4 h5 _ h6 _ _ g _ _ =>
      (SegW.ofSeg (hcallee R' F' h1 h2 h3 h4 h5 h6 g)).mono_post fun _ _ ⟨x, h⟩ => ⟨x, h, trivial⟩)
    hNe hent hret).toSeg

/-! ## Entering and leaving a callee's region

`call_nd_FWK`'s two halves as facts about one state, for a segment that
crosses a call without returning inside it (an allocation's continuation
lands in the callee). -/

/-- **The caller's cells outside the callee's region** (at `kc`, from `lo'`
to `hi'`) are as in `m0`. -/
def CKept (R : Region) (kc lo' hi' : Int) (m0 m : MachineData) : Prop :=
  ∀ k, R.Off k → ¬ (R.callee kc lo' hi').Off (k - kc) →
    Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt m0.dmem (R.addr k) 8

/-- **The callee's frame condition at a call** from the caller's state
`m0`, `σC` at offsets `o` (`sp` at `kc`): the caller's `F`, its cells
outside the callee's region as in `m0`, and `m0`, `σC` the caller's. No
write inside the callee's region breaks it. -/
theorem fstable_enter {kc lo' hi' : Int} {o : SO} {m0 : MachineData} {σC : AS}
    (hR : R.OK) (hF : FStable R F) (hlo : R.lo ≤ kc + lo') (hlo0 : lo' ≤ 0) (hkc : kc < R.hi) (hhi0 : hi' ≤ 0)
    (hk8 : kc % 8 = 0) (hl8 : lo' % 8 = 0) (hh8 : hi' % 8 = 0) :
    FStable (R.callee kc lo' hi') (fun m => F m ∧ CKept R kc lo' hi' m0 m ∧ Abs R o m0 σC) := fun m m' hm hd =>
  ⟨FStable.callee hR hlo hlo0 hkc (by omega) hF m m' hm.1 hd, fun k hk hn =>
    (hd _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkc hk8 hl8 hh8 hk hn)).trans (hm.2.1 k hk hn), hm.2.2⟩

/-- **Entering the callee's region**: a state at the call node `nC` is at
the callee's entry (`sp` at its region's base) in the region at the call,
under the callee's frame condition from it (`fstable_enter`), the abstract
state the caller's entered. -/
theorem at_enter {nC : ND} {lo' hi' : Int} (hlo : R.lo ≤ nC.o.sp + lo') (hkc : nC.o.sp < R.hi)
    (hhi0 : hi' ≤ 0) (hk8 : nC.o.sp % 8 = 0) {s : State} {c : Ctl} (h : At exe endPc R F nC s c) :
    ∃ m0 σC, At exe endPc (R.callee nC.o.sp lo' hi')
      (fun m => F m ∧ CKept R nC.o.sp lo' hi' m0 m ∧ Abs R nC.o m0 σC)
      ⟨nC.pc, ⟨0, []⟩, fun σ c' => c' = c ∧ σ = enter nC.o.sp σC ∧ nC.J σC c⟩ s c := by
  obtain ⟨he, hn, hdc, hpc, σC, hA, hD, hJ⟩ := h
  refine ⟨s.st.1, σC, he, hn, hdc, hpc, enter nC.o.sp σC, ⟨hA.regs, hA.status, ?_, fun k hk => ?_⟩,
    ⟨hD, fun _ _ _ => rfl, hA⟩, rfl, rfl, hJ⟩
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

/-- **Leaving the callee's region**: a state at a node `x` of the callee
(`sp` at its region's base), under a frame condition giving the caller's
`F`, its cells outside the callee's region as in a caller's state `m0`,
`σC` of `P`, is at `x`'s pc in the caller's region (`sp` at `kc`), the
abstract state the caller's left (`leave`). -/
theorem at_leave {kc lo' hi' : Int} {F' : MachineData → Prop} {P : AS → Prop} {x : ND} (hx : x.o = ⟨0, []⟩)
    (hF' : ∀ m, F' m → F m ∧ ∃ m0 σC o, CKept R kc lo' hi' m0 m ∧ Abs R o m0 σC ∧ P σC)
    {s : State} {c : Ctl} (h : At exe endPc (R.callee kc lo' hi') F' x s c) :
    At exe endPc R F ⟨x.pc, ⟨kc, []⟩, fun σ c => ∃ σx σC, x.J σx c ∧ P σC ∧
      σ = leave (R.callee kc lo' hi') kc σC σx⟩ s c := by
  obtain ⟨he, hn, hdc, hpc, σx, hAx, hD, hJx⟩ := h
  obtain ⟨hDF, m0, σC, o, hK, hAC, hP⟩ := hF' _ hD
  refine ⟨he, hn, hdc, hpc, leave (R.callee kc lo' hi') kc σC σx, ⟨hAx.regs, hAx.status, ?_, fun k hk => ?_⟩, hDF,
    σx, σC, hJx, hP, rfl⟩
  · intro r k' hr
    rcases r with y | _
    · cases hr
    · simp only [SO.get, Option.some.injEq] at hr
      subst hr
      have := hAx.so .SP _ (by rw [hx]; rfl)
      simp only [leave] at this ⊢
      rw [this, Region.callee_addr, Int.add_zero]
  · by_cases hin : (R.callee kc lo' hi').Off (k - kc)
    · obtain ⟨j, hj, hv⟩ := hAx.slot _ hin
      refine ⟨j, ?_, ?_⟩
      · rw [Region.callee_addr, show kc + (k - kc) = k by omega] at hj; exact hj
      · simp only [leave]; rw [ite_eq_left hin]; exact hv
    · obtain ⟨j, hj, hv⟩ := hAC.slot k hk
      refine ⟨j, ?_, ?_⟩
      · rw [hK k hk hin]; exact hj
      · simp only [leave]; rw [ite_eq_right hin]; exact hv

end Fn

end Spike.Lib.A64.Flow
