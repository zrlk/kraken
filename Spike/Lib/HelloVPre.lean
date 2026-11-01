/-
**hello.w: main's views below the memory size at the `spawn`, from the
start** (`VPreH`, `vpreH_spawn`; hello's `SpawnViewLtSteps.VPre`/`vpre_spawn`
twin).

Before the spawn, hello's source has one thread, main, at one of the stages
of `HelloPreTerm` (`HAt`). Every stage keeps main's views and coherence at
most the memory size minus one (`VB`): local steps, calls, returns and the
tail call keep the view state; the buffer's `newBuf` (stage 3) and the box's
`new` (18) push messages and raise coherence and the write view to them;
the lane exchanges (5, 7) load (the read view rises to the message's view
or its pair partner, both in memory by `TermViewInv.ViewInv` and
`TermPairLayout.PairInv`) then store; the publications (8, 19) raise the
release view to the write view. The same steps keep coherence covering the
memory (`CohM`, `VEff`'s second field, for the coherence invariant). At the
spawn the memory is nonempty and every environment word is a constant, so
main's views and words are strictly below the size (`vpreH_spawn`).

- `stepLoad_vb`, `stepStore_vb`: a plain load or a store keeps `VB` at the
  size minus one.
- `VEff`, `hat_veff`: a thread step of main from any stage grows memory,
  keeps `CohM` and `VB`.
- `VPreH`, `vpreH_init`, `vpreH_step`, `vpreH_run`, `pre1T_vpreH`: the
  invariant along source runs (vacuous once there are two threads).
- `vpreH_spawn`: `SpawnVLt` at every address and `EnvLt` at `spawnTermH`.
-/
import Spike.Lib.HelloVFlag
import Spike.Lib.SpawnCohSteps
import WeakCore.TermPairLayout

namespace Spike.Lib.HelloVPre

open CoreLang CoreTerm TermRun
open WeakMem (VState Address Ts Arch)
open Scc.Sem Scc.Sem.SrcSem
open Spike.Lib.HelloSrc (helloSrc helloS hello_start)
open Spike.Lib.HelloRodataSrc
open Spike.Lib.HelloMainPreSrc
open Spike.Lib.HelloPreTerm
open Spike.Lib.HelloVBuf (set!_self hat_not_ext hat_spawnTerm)
open Spike.Lib.SpawnViewLtSteps (VB EnvB EnvLt stepStore_vs alloc_vb)
open Spike.Lib.SpawnViewLt (SpawnVLt)
open Spike.Lib.SpawnCohSteps (CohM CohC cohM_store cohM_alloc)
open TermViewInv (MsgV)
open Spike.Lib (LocalStepS)
open Spike.Lib.Hello1RodataSrc (rdK1 rdK2 τ8 env0 envN bBind envA env1 env2 env3 env4 bufElem_b)

/-! ## Machine steps at `size - 1` -/

theorem cohM_mono {mem : WeakMem.Memory} {coh coh' : Address → Nat} {P : List Ts} (h : CohM mem coh P)
    (hc : ∀ b, coh b ≤ coh' b) : CohM mem coh' P :=
  fun k m hm hk => Nat.le_trans (h k m hm hk) (hc _)

/-- **A plain load keeps `VB` at `size - 1`** (messages' views at most their
index, pair entries' second words in memory). -/
theorem stepLoad_vb {arch : Arch} {mem : WeakMem.Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {dst : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg}
    (hm : MsgV mem) (hp : ∀ q ∈ pairs, q + 1 < mem.size) (hv : VB th.vs (mem.size - 1))
    (h : th' ∈ Promises.stepLoad arch mem pairs th dst a deps false) :
    VB th'.vs (mem.size - 1) := by
  unfold Promises.stepLoad at h
  simp only [List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨t, ⟨ht, -⟩, rfl⟩ := h
  have hmv : (mem[t]!).view ≤ t := TermViewInv.msg_view hm ht
  have hpt : Promises.pairTop pairs t ≤ mem.size - 1 := by
    unfold Promises.pairTop
    split
    · rename_i hc
      have := hp t (by simpa using hc)
      exact Nat.le_sub_one_of_lt this
    · exact Nat.le_sub_one_of_lt ht
  have hrd := Promises.rdV_le th.vs pairs t (mem[t]!).view
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
  refine ⟨?_, h2, h3, ?_, h5, fun b => ?_⟩
  · simp only [WeakMem.Ts] at *
    omega
  · simpa using h4
  · simp only
    split
    · have := h6 a
      simp only [WeakMem.Ts] at *
      omega
    · exact h6 b

/-- **A store keeps `VB` at `size - 1`.** -/
theorem stepStore_vb {k : Promises.Knobs} {arch : Arch} {mem mem' : WeakMem.Memory} {th th' : Promises.Thread}
    {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool} (hv : VB th.vs (mem.size - 1))
    (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel) :
    mem.size ≤ mem'.size ∧ VB th'.vs (mem'.size - 1) := by
  obtain ⟨t, hc, hcoh, hrel, hwr⟩ := TermStep.stepStore_casesC h
  obtain ⟨e1, e2, e3⟩ := stepStore_vs h
  have ht : t ≤ mem'.size - 1 ∧ mem.size ≤ mem'.size := by
    rcases hc with ⟨rfl, rfl, -⟩ | ⟨rfl, -, -, -, m, hm, -⟩
    · simp
    · have := TermLiveProps.lt_of_get hm
      omega
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
  refine ⟨ht.2, ?_⟩
  simp only [VB, e1, e2, e3, hrel, hwr, hcoh]
  simp only [WeakMem.Ts] at *
  refine ⟨by omega, by omega, by omega, by omega, by omega, fun b => ?_⟩
  split
  · omega
  · have := h6 b
    omega

/-! ## main's stages -/

section Stages

variable {g : G} {mem mem' : WeakMem.Memory} {pairs pairs' : List Ts} {th th' : TTh} {wo0 wo1 : Word}

/-- **A step's view effect**: memory grows; coherence keeps covering the
memory (`CohM`); the views stay at most the size minus one (`VB`), given
the messages' views (`MsgV`) and the pair entries in memory. -/
def VEff (mem : WeakMem.Memory) (pairs : List Ts) (th : TTh) (mem' : WeakMem.Memory) (th' : TTh) : Prop :=
  mem.size ≤ mem'.size ∧ (CohM mem th.vs.coh th.promises → CohM mem' th'.vs.coh th'.promises) ∧
    (MsgV mem → (∀ q ∈ pairs, q + 1 < mem.size) → VB th.vs (mem.size - 1) → VB th'.vs (mem'.size - 1))

theorem veff_eq (hm : mem' = mem) (hp : th'.promises = th.promises) (hv : th'.vs = th.vs) :
    VEff mem pairs th mem' th' := by
  subst hm
  exact ⟨Nat.le_refl _, fun h => by rw [hp, hv]; exact h, fun _ _ h => by rw [hv]; exact h⟩

/-- A store fence raises the release view to the write view. -/
theorem veff_fence (hm : mem' = mem) (hp : th'.promises = th.promises)
    (hv : th'.vs = (fenceS (stOf mem pairs th) .st).vs) : VEff mem pairs th mem' th' := by
  subst hm
  refine ⟨Nat.le_refl _, fun h => by rw [hp, hv]; exact h, fun _ _ h => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  rw [hv]
  simp only [fenceS, stOf, Promises.stepFence, mth]
  exact ⟨h1, h2, h3, h4, Nat.max_le.2 ⟨h5, h2⟩, h6⟩

theorem hatV_local {k : Nat} (hl : LocalStepS helloSrc (hc k wo0 wo1) (hc (k + 1) wo0 wo1)) (hg : g.p = helloSrc)
    (h : HAt th k wo0 wo1) (hr : (mem', pairs', th') ∈ tstep g mem pairs th) : VEff mem pairs th mem' th' := by
  obtain ⟨-, ht, he, hσ, -⟩ := h
  rw [hl.2 g mem pairs th hg ht he hσ, List.mem_singleton] at hr
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, -, rfl⟩ := hr
  exact veff_eq rfl rfl rfl

theorem hatV_call (hg : g.p = helloSrc) (h : HAt th 0 wo0 wo1) (hr : (mem', pairs', th') ∈ tstep g mem pairs th) :
    VEff mem pairs th mem' th' := by
  obtain ⟨-, ht, he, hσ, hs, hna⟩ := h
  simp only [hc] at ht he
  simp only [hfs] at hs
  obtain ⟨d, hd, hb, ha, hat, hrt⟩ := rd_decl
  simp [tstep, ht, Scc.Sem.SrcSem.setupTerm, callFrame, enter, hg, rodata_find, he, hσ, hs, hd, hb, ha, hat, hrt,
    envSU, evalAt, lookupE, ol] at hr
  obtain ⟨rfl, rfl, rfl⟩ := hr
  exact veff_eq rfl rfl rfl

theorem hatV_ret (h : HAt th 13 wo0 wo1) (hr : (mem', pairs', th') ∈ tstep g mem pairs th) :
    VEff mem pairs th mem' th' := by
  obtain ⟨-, ht, he, hσ, hs, hna⟩ := h
  simp only [hc, rdRet, eRet] at ht
  simp [tstep, ht, hs, hfs, he, hc, rdRet, envR, evalAt, lookupE] at hr
  obtain ⟨rfl, rfl, rfl⟩ := hr
  exact veff_eq rfl rfl rfl

theorem hatV_tail (hg : g.p = helloSrc) (h : HAt th 15 wo0 wo1) (hr : (mem', pairs', th') ∈ tstep g mem pairs th) :
    VEff mem pairs th mem' th' := by
  obtain ⟨-, ht, he, hσ, hs, hna⟩ := h
  simp only [hc] at ht
  simp [tstep, ht, enter, hg, main_findH, he, hc, evalAt, lookupE, ol] at hr
  obtain ⟨rfl, rfl, rfl⟩ := hr
  exact veff_eq rfl rfl rfl

theorem hatV_pubB (h : HAt th 8 wo0 wo1) (hr : (mem', pairs', th') ∈ tstep g mem pairs th) :
    VEff mem pairs th mem' th' := by
  obtain ⟨-, ht, he, hσ, hs, hna⟩ := h
  rw [TermLocal.tstep_let_gen ht rfl] at hr
  simp [evalOp, he, ol, hc, rdC4, env4, env3, env2, env1, envA, bBind, evalAt, lookupE] at hr
  obtain ⟨rfl, rfl, rfl⟩ := hr
  exact veff_fence rfl rfl rfl

theorem hatV_pubX (h : HAt th 19 wo0 wo1) (hr : (mem', pairs', th') ∈ tstep g mem pairs th) :
    VEff mem pairs th mem' th' := by
  obtain ⟨-, ht, he, hσ, hs, hna⟩ := h
  rw [TermLocal.tstep_let_gen ht rfl] at hr
  simp [evalOp, he, ol, hc, envO, evalAt, lookupE] at hr
  obtain ⟨rfl, rfl, rfl⟩ := hr
  exact veff_fence rfl rfl rfl

theorem hatV_newBuf (hb : g.lbase = 0) (hn : g.n = 2) (hi : g.i = 0) (h : HAt th 3 wo0 wo1)
    (hr : (mem', pairs', th') ∈ tstep g mem pairs th) : VEff mem pairs th mem' th' := by
  obtain ⟨-, ht, he, hσ, hs, hna⟩ := h
  rw [TermLocal.tstep_let_gen ht rfl] at hr
  have ha : accs (close [] τ8) = some [.one] := rfl
  simp [evalOp, he, hσ, hc, rdCN, envN, evalAt, lookupE, numOf, ol, allocBuf, zeroable8, zeroWords8, ha, lbB_eq,
    hb, hn, hi, stOf, hna, Spike.Lib.HelloPreTerm.hna] at hr
  obtain ⟨rfl, rfl, rfl⟩ := hr
  have hn1 : nWords [Acc.one] = 1 := rfl
  simp only [hn1, Nat.mul_one]
  refine ⟨by simp, fun hc k m hm hk => ?_, fun _ _ hv => ?_⟩
  · simp only [withS] at hk ⊢
    rw [Array.getElem?_append] at hm
    split at hm
    · rename_i hlt
      have := hc k m hm hk
      split
      · exact Nat.le_trans (Nat.le_of_lt hlt) (Nat.le_add_right _ _)
      · exact this
    · rename_i hge
      simp only [List.getElem?_toArray, List.getElem?_map] at hm
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hm
      have hj2 := (List.getElem?_eq_some_iff.mp hj)
      obtain ⟨hl, hjv⟩ := hj2
      simp only [List.length_range, List.getElem_range] at hl hjv
      subst hjv
      simp only [offs, Nat.zero_add, hl, and_self, ↓reduceIte]
      simp only [WeakMem.Ts] at *
      omega
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
    simp only [VB, withS, Array.size_append, List.size_toArray, List.length_map, List.length_range]
    simp only [WeakMem.Ts] at *
    refine ⟨by omega, by omega, by omega, by omega, by omega, fun b => ?_⟩
    split
    · rename_i hb
      exact Nat.le_sub_one_of_lt (Nat.add_lt_add_left hb.2 _)
    · exact Nat.le_trans (h6 b) (Nat.sub_le_sub_right (Nat.le_add_right _ _) 1)

/-- A lane exchange: a plain load, then a store, at the buffer's word. -/
theorem veff_xchg {arch : Arch} {k : Promises.Knobs} {a : Address} {e : WeakMem.Expr} {pw w0 w1 : Word}
    {t1 : Promises.Thread} {mem2 : WeakMem.Memory} {t2 : Promises.Thread} {u : Nat}
    (hl : t1 ∈ Promises.stepLoad arch mem pairs (mth (stOf mem pairs th) pw pw pw) 1 a [0] false)
    (hst : (mem2, t2) ∈ Promises.stepStore k arch mem
      (mth { stOf mem pairs th with vs := t1.vs, undefs := u } pw w0 w1) a e [0] false)
    (hm : mem' = mem2) (hp : th'.promises = t2.promises) (hv : th'.vs = t2.vs) : VEff mem pairs th mem' th' := by
  subst hm
  have hc1 := stepLoad_coh hl
  refine ⟨?_, fun hc => ?_, fun hmv hpq hvb => ?_⟩
  · obtain ⟨t, hcase, -⟩ := TermStep.stepStore_casesC hst
    rcases hcase with ⟨rfl, -, -⟩ | ⟨rfl, -⟩
    · simp
    · exact Nat.le_refl _
  · rw [hp, hv]
    exact cohM_store (th := mth { stOf mem pairs th with vs := t1.vs, undefs := u } pw w0 w1)
      (cohM_mono hc hc1) hst
  · rw [hv]
    have h1 : VB t1.vs (mem.size - 1) := stepLoad_vb hmv hpq hvb hl
    exact (stepStore_vb (th := mth { stOf mem pairs th with vs := t1.vs, undefs := u } pw w0 w1) h1 hst).2

theorem hatV_xchg0 (h : HAt th 5 wo0 wo1) (hr : (mem', pairs', th') ∈ tstep g mem pairs th) :
    VEff mem pairs th mem' th' := by
  obtain ⟨-, ht, he, hσ, hs, hna⟩ := h
  rw [TermLocal.tstep_let_gen ht rfl] at hr
  have ha : accs τ8 = some [.one] := rfl
  simp [evalOp, he, hc, rdC1, env1, envA, bBind, evalAt, lookupE, numOf, addrOf, ha, bufElem_b] at hr
  obtain ⟨s2, t, ws, hm, rfl, rfl, rfl⟩ := hr
  simp [loadUnits, storeUnits, offs, dataE, cst] at hm
  obtain ⟨s1, b, ⟨t1, hl, rfl, rfl⟩, s2', ⟨mem2, t2, hst, rfl⟩, rfl, rfl, rfl⟩ := hm
  exact veff_xchg hl hst rfl rfl rfl

theorem hatV_xchg1 (h : HAt th 7 wo0 wo1) (hr : (mem', pairs', th') ∈ tstep g mem pairs th) :
    VEff mem pairs th mem' th' := by
  obtain ⟨-, ht, he, hσ, hs, hna⟩ := h
  rw [TermLocal.tstep_let_gen ht rfl] at hr
  have ha : accs τ8 = some [.one] := rfl
  simp [evalOp, he, hc, rdC3, env3, env2, env1, envA, bBind, evalAt, lookupE, numOf, addrOf, ha, bufElem_b] at hr
  obtain ⟨s2, t, ws, hm, rfl, rfl, rfl⟩ := hr
  simp [loadUnits, storeUnits, offs, dataE, cst] at hm
  obtain ⟨s1, b, ⟨t1, hl, rfl, rfl⟩, s2', ⟨mem2, t2, hst, rfl⟩, rfl, rfl, rfl⟩ := hm
  exact veff_xchg hl hst rfl rfl rfl

theorem hatV_new (hb : g.lbase = 0) (hn : g.n = 2) (hi : g.i = 0) (h : HAt th 18 wo0 wo1)
    (hr : (mem', pairs', th') ∈ tstep g mem pairs th) : VEff mem pairs th mem' th' := by
  obtain ⟨-, ht, he, hσ, hs, hna⟩ := h
  obtain ⟨_, _, _, hr, tys, hr'⟩ := TermRun.tstep_new_mem ht hr
  have hl : freshLabel g.lbase g.n g.i th.nalloc = lbX := by rw [hb, hn, hi, hna]; rfl
  simp only [evalOp, he, hc, c0H, evalAt, lookupE, List.find?] at hr
  have hacc : accs .int = some [.one] := rfl
  simp only [show ("z" == "z") = true from rfl, Option.map_some, hacc, List.map_map, List.mem_map,
    Function.comp_def] at hr
  obtain ⟨⟨s2, pw⟩, ha, he2⟩ := hr
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  simp only [Prod.mk.injEq] at hr'
  obtain ⟨rfl, rfl, rfl⟩ := hr'
  have ha' : (s2, pw) ∈ alloc g.k g.arch lbX [.one] [cst (.num 0)] (stOf mem pairs th) := by
    rw [← hl]; exact ha
  refine ⟨?_, fun hc => cohM_alloc (s := stOf mem pairs th) hc ha', fun _ _ hv => ?_⟩
  · exact Nat.le_of_lt (alloc_boxE ha').1
  · exact (alloc_vb (s := stOf mem pairs th) hv ha').2.1

/-- **A thread step from stage `k` has `VEff`** (at main's `G`). -/
theorem hat_veff {k : Nat} (hg : g.p = helloSrc) (hb : g.lbase = 0) (hn : g.n = 2) (hi : g.i = 0)
    (h : HAt th k wo0 wo1) (hr : (mem', pairs', th') ∈ tstep g mem pairs th) : VEff mem pairs th mem' th' := by
  match k, h.1 with
  | 0, _ => exact hatV_call hg h hr
  | 1, _ => exact hatV_local (hc_local 1 (by decide)) hg h hr
  | 2, _ => exact hatV_local (hc_local 2 (by decide)) hg h hr
  | 3, _ => exact hatV_newBuf hb hn hi h hr
  | 4, _ => exact hatV_local (hc_local 4 (by decide)) hg h hr
  | 5, _ => exact hatV_xchg0 h hr
  | 6, _ => exact hatV_local (hc_local 6 (by decide)) hg h hr
  | 7, _ => exact hatV_xchg1 h hr
  | 8, _ => exact hatV_pubB h hr
  | 9, _ => exact hatV_local (hc_local 9 (by decide)) hg h hr
  | 10, _ => exact hatV_local (hc_local 10 (by decide)) hg h hr
  | 11, _ => exact hatV_local (hc_local 11 (by decide)) hg h hr
  | 12, _ => exact hatV_local (hc_local 12 (by decide)) hg h hr
  | 13, _ => exact hatV_ret h hr
  | 14, _ => exact hatV_local (hc_local 14 (by decide)) hg h hr
  | 15, _ => exact hatV_tail hg h hr
  | 16, _ => exact hatV_local (hc_local 16 (by decide)) hg h hr
  | 17, _ => exact hatV_local (hc_local 17 (by decide)) hg h hr
  | 18, _ => exact hatV_new hb hn hi h hr
  | 19, _ => exact hatV_pubX h hr
  | 20, _ => exact hatV_local (hc_local 20 (by decide)) hg h hr
  | 21, _ => exact hatV_local (hc_local 21 (by decide)) hg h hr
  | 22, _ => exact (hat_spawn h hr).elim
  | _ + 23, hk => omega

/-- The spawn stage's words are constants. -/
theorem hc22_env : ∀ p ∈ (hc 22 wo0 wo1).env, ∀ w ∈ p.2.2, w.view = 0 ∧ w.rts = 0 := by
  intro p hp w hw
  simp only [hc, envP0, envC, envO, c0H, envS, slW, meW, List.mem_cons, List.not_mem_nil, or_false] at hp
  have key : ∀ ws : List Word, (∀ w ∈ ws, w.view = 0 ∧ w.rts = 0) → w ∈ ws → w.view = 0 ∧ w.rts = 0 :=
    fun ws h hw => h w hw
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact key _ (by simp [cst, Promises.TVal.mk0]) hw

end Stages

/-! ## Along source runs -/

/-- **hello's pre-spawn view invariant** (`SpawnViewLtSteps.VPre`'s twin):
with one thread, main is at a stage `k` of `HAt` (label base 0, capacity
2); the configuration has the generic view and pair-layout invariants
(`TermViewInv.ViewInv`, `TermPairLayout.PairInv`); main's views and
coherence are at most the memory size minus one (`VB`); the memory is
nonempty from the box's publication (stage 19) on.

Against wake's `TInv`: `MainPre` and `stack = []` are replaced by `HAt`
(which fixes the term, environment and frames: `frS` at stages 1-13);
`z : Int` at `new` is implied by `HAt` at stage 18; `EnvB` is not carried
(at the spawn every environment word is a constant, `hc22_env`, so
`EnvLt` follows from `0 < size`); `term ∈ {mO, mC, spawnTerm} → 0 < n` is
`19 ≤ k → 0 < size`. `ViewInv` and `PairInv` are hello-only: they bound the
loaded words' views at the lane exchanges (wake has no load). -/
def VPreH (s : Cfg) : Prop :=
  s.ths.size = 1 → ∃ th0 k wo0 wo1, s.ths[0]? = some th0 ∧ s.lbase = 0 ∧ s.cap = 2 ∧ HAt th0 k wo0 wo1 ∧
    TermViewInv.ViewInv s ∧ TermPairLayout.PairInv s ∧ VB th0.vs (s.mem.size - 1) ∧ (19 ≤ k → 0 < s.mem.size)

theorem vpreH_init {arch : Arch} {s : Cfg} (h : (helloS arch).init s) : VPreH s := by
  have h' : s = Spike.Lib.WakeT1.setupStartT 2 := by
    change Spike.Lib.WakeT1.progInitT helloSrc 2 s at h
    rw [hello_start] at h
    exact h
  subst h'
  intro _
  refine ⟨_, 0, meW, meW, rfl, rfl, rfl, hat_start, ?_, ?_, ?_, fun h => absurd h (by decide)⟩
  · refine TermViewInv.viewInv_init rfl fun i th hth => ?_
    obtain rfl : i = 0 := by have := TermLiveProps.lt_of_get hth; simp [Spike.Lib.WakeT1.setupStartT] at this; omega
    simp only [Spike.Lib.WakeT1.setupStartT] at hth
    cases hth
    refine ⟨rfl, ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩, fun e he w hw => ?_⟩
    simp only [List.getElem_toArray, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · simp only [List.mem_singleton] at hw; subst hw; exact ⟨rfl, rfl⟩
    · simp at hw
  · refine TermPairLayout.pairInv_nil rfl fun i th hth => ?_
    obtain rfl : i = 0 := by have := TermLiveProps.lt_of_get hth; simp [Spike.Lib.WakeT1.setupStartT] at this; omega
    simp only [Spike.Lib.WakeT1.setupStartT] at hth
    cases hth
    rfl
  · exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, fun _ => Nat.zero_le _⟩

/-- **One source step keeps `VPreH`.** -/
theorem vpreH_step {arch : Arch} {i : Nat} {s s' : Cfg} {es : List Ev} (h : (helloS arch).step i s es s')
    (hv : VPreH s) : VPreH s' := by
  intro h1'
  obtain ⟨-, hs, -⟩ := h
  rcases hs with hs | hs | hs
  · have h1 : s.ths.size = 1 := stepBy_size hs ▸ h1'
    obtain ⟨th0, k, wo0, wo1, h0, hb, hcap, hat, hvi, hpi, hvb, hn0⟩ := hv h1
    have hvi' := TermViewInv.viewInv_step hvi hs.step
    have hpi' := (TermPairLayout.pairStep_step (cap := 0) hpi (Or.inl hs.step)).1
    rcases hs with ⟨hm, -⟩ | ⟨a, v, w, hi', -, -, rfl⟩
    · unfold TermRun.threadSteps at hm
      split at hm
      · simp at hm
      · rename_i th hth
        obtain rfl : i = 0 := by have := (Array.getElem?_eq_some_iff.mp hth).1; omega
        rw [h0] at hth
        cases hth
        obtain ⟨⟨mem, pairs, th'⟩, hr, rfl⟩ := List.mem_map.mp hm
        have hn : s.n = 2 := by simp [Cfg.n, hcap, h1]
        obtain ⟨wo0', wo1', hat', he⟩ := hat_tstep rfl hb hn rfl hat hr
        obtain ⟨hsz, -, hV⟩ := hat_veff rfl hb hn rfl hat hr
        have hq : ∀ q ∈ s.pairs, q + 1 < s.mem.size := fun q hq => by
          obtain ⟨m0, m1, -, h1, -⟩ := hpi.1 q hq
          exact TermLiveProps.lt_of_get h1
        refine ⟨th', k + 1, wo0', wo1', set!_self h0 _, hb, hcap, hat', hvi', hpi', hV hvi.1 hq hvb, fun hk => ?_⟩
        by_cases h18 : k = 18
        · subst h18
          exact Nat.lt_of_le_of_lt (Nat.zero_le _) he.1
        · exact Nat.lt_of_lt_of_le (hn0 (by omega)) hsz
    · obtain rfl : i = 0 := by omega
      unfold TermRun.promise at hvi' hpi' ⊢
      rw [h0] at hvi' hpi' ⊢
      refine ⟨_, k, wo0, wo1, set!_self h0 _, hb, hcap, hat, hvi', hpi', hvb.mono (by simp), fun hk => by simp⟩
  · have := (spawnBy_size hs).1
    obtain ⟨x, f, a, T, ts, e, th, rt, ws, hth, -⟩ := hs
    have := (Array.getElem?_eq_some_iff.mp hth).1
    omega
  · obtain ⟨x, n, a, e, th, rt, ws, rs, hth, hterm, -, -, -, -, rfl⟩ := hs
    have h1 : s.ths.size = 1 := by rwa [TermExtStep.wake_size, TermExtStep.extCfg_size] at h1'
    obtain ⟨th0, k, wo0, wo1, h0, -, -, hat, -⟩ := hv h1
    obtain rfl : i = 0 := by have := (Array.getElem?_eq_some_iff.mp hth).1; omega
    rw [h0] at hth
    cases hth
    exact (hat_not_ext hat hterm).elim

/-- **`VPreH` along source runs.** -/
theorem vpreH_run {arch : Arch} {s s' : Cfg} {tr : List Ev} (h : (helloS arch).Run s tr s') (hv : VPreH s) :
    VPreH s' := by
  induction h with
  | refl => exact hv
  | step hs _ ih =>
    obtain ⟨i, hs⟩ := hs
    exact ih (vpreH_step hs hv)

open Spike.Lib.WakePreTi (Pre1T) in
/-- **`Pre1T` with `VPreH`** (any hello `Pre1T`). -/
theorem pre1T_vpreH {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {E : Entry}
    {R1 : Spike.Lib.WakeA64.Cfg → TermRun.Cfg → Prop} {Ab Ac : Kraken.Promising.AArch64.State → Prop}
    (O : Pre1T arch Λ B asm E R1 Ab Ac helloSrc) :
    Pre1T arch Λ B asm E (fun d s => R1 d s ∧ VPreH s) Ab Ac helloSrc :=
  Spike.Lib.WakePreInv.Pre1T.invSrc O VPreH (fun _ h => vpreH_init h) (fun _ _ _ hr hv => vpreH_run hr hv)

/-! ## At the spawn -/

/-- **Strict bounds at main's spawn** (`SpawnViewLtSteps.vpre_spawn`'s
shape): with one thread, at `spawnTermH`, main's views (`SpawnVLt`, at every
address) and its environment's words (`EnvLt`) are below the memory size. -/
theorem vpreH_spawn {s : Cfg} {th0 : TTh} (hv : VPreH s) (h1 : s.ths.size = 1) (h0 : s.ths[0]? = some th0)
    (ht : th0.term = spawnTermH) : (∀ a, SpawnVLt th0 a s.mem.size) ∧ EnvLt th0 s.mem.size := by
  obtain ⟨th, k, wo0, wo1, h0', -, -, hat, -, -, ⟨h1, h2, h3, h4, h5, h6⟩, hn⟩ := hv h1
  rw [h0] at h0'; cases h0'
  obtain rfl := hat_spawnTerm hat ht
  have hn := hn (by decide)
  refine ⟨fun a => ?_, fun p hp w hw => ?_⟩
  · have h6 := h6 a
    simp only [SpawnVLt, WeakMem.Ts] at *
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · rw [hat.2.2.1] at hp
    obtain ⟨e1, e2⟩ := hc22_env p hp w hw
    rw [e1, e2]
    exact ⟨hn, hn⟩

/-- info: 'Spike.Lib.HelloVPre.pre1T_vpreH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pre1T_vpreH

/-- info: 'Spike.Lib.HelloVPre.vpreH_spawn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vpreH_spawn

end Spike.Lib.HelloVPre
