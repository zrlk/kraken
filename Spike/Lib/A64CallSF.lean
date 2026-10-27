/-
**A machine call node whose callee returns at any frames** (AArch64; the
twin of `Spike/Lib/X64CallSF.lean`): `call_nd_FWKS`
(`Spike/Lib/A64CallS.lean`) with the callee's exits at the frames the source
has when the machine returns, not the caller's: a callee whose source is
held back inside a call of its own (a pending frame, e.g. `print`'s `ret ()`
still to take at `scc_rt_main`'s `exit_group`) returns on the machine while
the source is still at depth.

- `call_nd_FWKSF`: the callee's specification a segment from its entry at
  the caller's frames `fs` to its exits `Ex g fs' x` at any frames `fs'`;
  the caller's nodes after the return indexed by those frames (`N fs'`,
  `E fs'`);
- `MainGFr`, `MainGFr.ret`: its callee's ghost frame condition, named, and
  the return to the caller's nodes from an exit under it;
- `call_nd_FWKSFG`: `call_nd_FWKSF` with the callee at `MainGFr`.
-/
import Spike.Lib.A64CallS

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _}
  {N : List TermRun.Frame → ι → ND} {E : List TermRun.Frame → κ → ND}

open Classical in
/-- **A machine call node at fixed frames whose callee returns at any
frames** (`call_nd_FWKS` with the exits' frames free): the callee runs from
the caller's frames `fs`, its specification a segment to its exits `Ex g fs'
x` at the frames `fs'` the source has at the return; the return lands on the
caller's nodes at those frames (`N fs'`, `E fs'`). -/
theorem call_nd_FWKSF {KC : Prop} {W : FragS isaLSE2} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {nC : ND} {γ : Type _} {κ' : Sort _} {lo' hi' : Int} {Ne : γ → ND}
    {Ex : γ → List TermRun.Frame → κ' → ND} {fs : List TermRun.Frame}
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
        SegWS W K p lbl ms ((At exe endPc R' F' (Ne g)).at fs)
          (fun s c fs' => ∃ x, At exe endPc R' F' (Ex g fs' x) s c ∧ M s.st.1))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter nC.o.sp σC) c)
    (hret : ∀ g fs' x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter nC.o.sp σC) c →
      (Ex g fs' x).J σx c' → σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands (N fs') (E fs') ⟨(Ex g fs' x).pc, ⟨nC.o.sp + (Ex g fs' x).o.sp, []⟩, σR⟩ c') :
    SegWS W K p lbl ms ((At exe endPc R F nC).at fs)
      (fun s c fs' => Next exe endPc R F₂ (N fs') (E fs') s c) := by
  let kc := nC.o.sp
  let R' := R.callee kc lo' hi'
  have hR' : R'.OK := Region.callee_ok hR hlo hlo0 hkc (by omega)
  have hb' := Region.callee_base (hi' := hi') hR hlo hlo0 hkc
  have hal' : R'.base.toNat % 16 = 0 := by
    have : ((R'.base.toNat : Int)) % 16 = 0 := by rw [hb']; omega
    omega
  have hFR' : FStable R' F := FStable.callee hR hlo hlo0 hkc (by omega) hF
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
  refine SegWS.mono_pre (P := fun s c fs' => ∃ G, (At exe endPc R' (F' G) (Ne G.2.2.2)).at fs s c fs')
    (SegWS.exists_pre fun G => ?_) ?_
  · by_cases hG : nC.J G.2.1 G.2.2.1 ∧ (Ne G.2.2.2).J (enter kc G.2.1) G.2.2.1
    · refine (hcallee R' (F' G) hR' hal' (Int.le_refl _) (Int.le_refl _) (hF' G) (fun hc => hK' hc G) (fun _ h => h.1)
        rfl (fun m hm k hk hn => by
          obtain ⟨j, hj, -⟩ := hm.2.2.1.slot k hk
          rw [hm.2.1 k hk hn, hj]; rfl) G.2.2.2 ⟨G.2.1, G.2.2.1, hG⟩
        (fun m hm => ⟨G.1, G.2.1, G.2.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2, hm.2.1⟩)).mono_post ?_
      rintro s c fs' ⟨x, ⟨he, hn, hdc, hpc, σx, hAx, ⟨hD, hDF, hAC, hJC, hJE⟩, hJx⟩, hM⟩
      obtain ⟨mC, σC, cC, g⟩ := G
      simp only at hDF hAC hJC hJE hJx hAx hpc
      have hAR : Abs R ⟨kc + (Ex g fs' x).o.sp, []⟩ s.st.1 (leave R' kc σC σx) := by
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
      have hL := hret g fs' x σC cC σx c (leave R' kc σC σx) hJC hJE hJx rfl rfl
        (fun k _ hn => by simp only [leave]; exact ite_eq_right hn)
      have hs : s = { s with st := (s.st.1, (Ex g fs' x).pc) } := by rw [← hpc]; rfl
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

/-- **The callee's ghost frame condition at a machine call** (`call_nd_FWKSF`'s,
named): at the ghost `G` (the machine data `G.1` and abstract state `G.2.1`
at the call node `nC`, the caller's control `G.2.2.1`, the callee's
parameters `G.2.2.2`), the caller's `F`, the caller's cells outside the
callee's region `R.callee kc lo' hi'` as in `G.1`, the caller's state at
`nC` (`Abs`, `nC.J`) and the callee's entry node holding at the caller's
control. The machine-call twin of `CallGF` (no source call). -/
def MainGFr {γ : Type _} (R : Region) (F : MachineData → Prop) (nC : ND) (lo' hi' : Int) (Ne : γ → ND)
    (G : MachineData × AS × Ctl × γ) (m : MachineData) : Prop :=
  F m ∧ (∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) →
      Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt G.1.dmem (R.addr k) 8) ∧
    Abs R nC.o G.1 G.2.1 ∧ nC.J G.2.1 G.2.2.1 ∧ (Ne G.2.2.2).J (enter nC.o.sp G.2.1) G.2.2.1

/-- **The return to the caller from an exit under the ghost frame
condition** (`call_nd_FWKSF`'s return): at an exit `Ex g fs' x` of the
callee in its region at the frames `fs'`, its frame condition `MainGFr` at
the ghost `G`, the machine lands at a caller's node at those frames at `F₂`
(the caller's abstract state rebuilt as `leave` of the call's and the
exit's). -/
theorem MainGFr.ret {F₂ : MachineData → Prop} {nC : ND} {γ : Type _} {κ' : Sort _} {lo' hi' : Int}
    {Ne : γ → ND} {Ex : γ → List TermRun.Frame → κ' → ND}
    (hret : ∀ g fs' x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter nC.o.sp σC) c →
      (Ex g fs' x).J σx c' → σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands (N fs') (E fs') ⟨(Ex g fs' x).pc, ⟨nC.o.sp + (Ex g fs' x).o.sp, []⟩, σR⟩ c')
    {G : MachineData × AS × Ctl × γ} {fs' : List TermRun.Frame} {x : κ'} {s : State} {c : Ctl}
    (hAt : At exe endPc (R.callee nC.o.sp lo' hi') (MainGFr R F nC lo' hi' Ne G) (Ex G.2.2.2 fs' x) s c)
    (hF₂ : F₂ s.st.1) :
    Next exe endPc R F₂ (N fs') (E fs') s c := by
  obtain ⟨mC, σC, cC, g⟩ := G
  obtain ⟨he, hn, hdc, hpc, σx, hAx, ⟨-, hDF, hAC, hJC, hJE⟩, hJx⟩ := hAt
  let kc := nC.o.sp
  let R' := R.callee kc lo' hi'
  have hAR : Abs R ⟨kc + (Ex g fs' x).o.sp, []⟩ s.st.1 (leave R' kc σC σx) := by
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
  have hL := hret g fs' x σC cC σx c (leave R' kc σC σx) hJC hJE hJx rfl rfl
    (fun k _ hn => by simp only [leave]; exact ite_eq_right hn)
  have hs : s = { s with st := (s.st.1, (Ex g fs' x).pc) } := by rw [← hpc]
  rw [hs]
  rcases hL with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hAR hF₂⟩
  · exact .inr ⟨y, hy.at he hn hdc hAR hF₂⟩

open Classical in
/-- **`call_nd_FWKSF` with the callee at the ghost frame condition**: the
callee's specification (`hcallee`) may assume its frame condition `F'` is
the call's ghost frame condition `MainGFr` at a ghost `G` whose parameters
are the callee's (e.g. for the callee's bottom frames to return to the
caller from a landing, `MainGFr.ret`); `call_nd_FWKSF` is this at a
callee's specification for every `F'`. -/
theorem call_nd_FWKSFG {KC : Prop} {W : FragS isaLSE2} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {nC : ND} {γ : Type _} {κ' : Sort _} {lo' hi' : Int} {Ne : γ → ND}
    {Ex : γ → List TermRun.Frame → κ' → ND} {fs : List TermRun.Frame}
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
        (∃ G, F' = MainGFr R F nC lo' hi' Ne G ∧ G.2.2.2 = g) →
        (∃ σC c, nC.J σC c ∧ (Ne g).J (enter nC.o.sp σC) c) →
        (∀ m, F' m → ∃ mC σC c, Abs R nC.o mC σC ∧ nC.J σC c ∧ (Ne g).J (enter nC.o.sp σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - nC.o.sp) → Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegWS W K p lbl ms ((At exe endPc R' F' (Ne g)).at fs)
          (fun s c fs' => ∃ x, At exe endPc R' F' (Ex g fs' x) s c ∧ M s.st.1))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, nC.J σC c → ∃ g, (Ne g).pc = nC.pc ∧ (Ne g).J (enter nC.o.sp σC) c)
    (hret : ∀ g fs' x σC c σx c' (σR : AS), nC.J σC c → (Ne g).J (enter nC.o.sp σC) c →
      (Ex g fs' x).J σx c' → σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp lo' hi').Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands (N fs') (E fs') ⟨(Ex g fs' x).pc, ⟨nC.o.sp + (Ex g fs' x).o.sp, []⟩, σR⟩ c') :
    SegWS W K p lbl ms ((At exe endPc R F nC).at fs)
      (fun s c fs' => Next exe endPc R F₂ (N fs') (E fs') s c) := by
  let kc := nC.o.sp
  let R' := R.callee kc lo' hi'
  have hR' : R'.OK := Region.callee_ok hR hlo hlo0 hkc (by omega)
  have hb' := Region.callee_base (hi' := hi') hR hlo hlo0 hkc
  have hal' : R'.base.toNat % 16 = 0 := by
    have : ((R'.base.toNat : Int)) % 16 = 0 := by rw [hb']; omega
    omega
  have hFR' : FStable R' F := FStable.callee hR hlo hlo0 hkc (by omega) hF
  let F' := MainGFr R F nC lo' hi' Ne
  have hF' : ∀ G, FStable R' (F' G) := fun G m m' hm hd =>
    ⟨hFR' m m' hm.1 hd, fun k hk hn =>
      (hd _ (R.addr_fit hR hk) (Region.callee_sep hR hlo hlo0 hkc (by omega) hl8 hh8 hk hn)).trans
        (hm.2.1 k hk hn), hm.2.2⟩
  have hK' : KC → ∀ G, KStable K (F' G) := fun hc G s s' hk hm =>
    ⟨hFK hc s s' hk hm.1, fun k hk' hn => (hKR hc s s' hk hm.1 k hk' hn).trans (hm.2.1 k hk' hn), hm.2.2⟩
  refine SegWS.mono_pre (P := fun s c fs' => ∃ G, (At exe endPc R' (F' G) (Ne G.2.2.2)).at fs s c fs')
    (SegWS.exists_pre fun G => ?_) ?_
  · by_cases hG : nC.J G.2.1 G.2.2.1 ∧ (Ne G.2.2.2).J (enter kc G.2.1) G.2.2.1
    · refine (hcallee R' (F' G) hR' hal' (Int.le_refl _) (Int.le_refl _) (hF' G) (fun hc => hK' hc G) (fun _ h => h.1)
        rfl (fun m hm k hk hn => by
          obtain ⟨j, hj, -⟩ := hm.2.2.1.slot k hk
          rw [hm.2.1 k hk hn, hj]; rfl) G.2.2.2 ⟨G, rfl, rfl⟩ ⟨G.2.1, G.2.2.1, hG⟩
        (fun m hm => ⟨G.1, G.2.1, G.2.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2, hm.2.1⟩)).mono_post ?_
      rintro s c fs' ⟨x, hAt, hM⟩
      have hD : F s.st.1 := by obtain ⟨-, -, -, -, -, -, hD, -⟩ := hAt; exact hD.1
      exact MainGFr.ret (F₂ := F₂) hret hAt (hF₂ _ hD hM)
    · exact SegWS.empty fun s c fs' ⟨⟨_, _, _, _, _, _, ⟨_, _, _, hJC, hJE⟩, _⟩, _⟩ => hG ⟨hJC, hJE⟩
  · rintro s c fs' ⟨⟨he, hn, hdc, hpc, σC, hA, hD, hJ⟩, rfl⟩
    obtain ⟨g, hgpc, hgJ⟩ := hent σC c hJ
    refine ⟨(s.st.1, σC, c, g), ⟨he, hn, hdc, by rw [hpc, hgpc], enter kc σC, ?_,
      ⟨hD, fun _ _ _ => rfl, hA, hJ, hgJ⟩, hgJ⟩, rfl⟩
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

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.A64.Flow.call_nd_FWKSF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms call_nd_FWKSF

/--
info: 'Spike.Lib.A64.Flow.call_nd_FWKSFG' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms call_nd_FWKSFG

end Spike.Lib.A64.Flow
