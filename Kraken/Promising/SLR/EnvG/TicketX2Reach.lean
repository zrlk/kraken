/-
**The per-thread invariant at every
reachable configuration.** ISA-generic.

`Inv Sp ini cf`: every message of `cf` is by one of its threads, the initial
memory is `ini`, and every thread `tid` is in a protocol state `g` with the
program specification `Sp tid g` at its ISA state and the invariant
`JTk x o c tid g` (`EnvG/TicketX2Env.lean`) of its views, promises and the
memory. The specification is a parameter: all this file asks of it is that
every instruction from it runs (`RunOK`) to a leaf where it holds again,
keeping `JC M0` from every memory `M0` (`hstep`); `EnvG/X64Ticket2VCGen.lean`
gets this from the `vcgen` run of the worker through `TreeJ.runJ` and
`runSim`.

- `stepOne_runV`: `stepOne_run` with the views of the outcome (those of the
  run but `vCAP`, `finishInstr_relKey`).
- `JTk.other`: another thread's step (the memory grows by messages of
  another thread) keeps a thread's invariant.
- **`Bk.promise`** (the promise step): the promised message, appended at
  `|M| + 1` with the thread's id, is an outstanding promise of the thread
  (it joins `P`); no recorded write is at `|M| + 1`.
- **`inv_step`**, **`inv_reachable`**: `Inv` survives instruction steps
  (`hstep` for the stepping thread, `JTk.other` for the rest) and promise
  steps (`Bk.promise`, `JTk.other`); `inv_init`: it holds initially.
-/
import Kraken.Promising.SLR.EnvG.TicketX2Env
import Kraken.Promising.SLR.StepRunCommon
import Kraken.Promising.SLR.Adequacy

namespace Kraken.Promising.SLR.EnvG.TicketX2

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

variable {I : ISA} {x o c : BitVec 64}

/-! ## One instruction, with the views -/

/-- `stepOne_run` with the outcome's views: those of the run, but `vCAP`. -/
theorem stepOne_runV (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) :
    ∃ tree iv c', I.exec t.st = some tree ∧
      .ok (o.thread.st, c') ∈
        runTree A tid iv { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } tree ∧
      o.thread.prom = c'.prom ∧ ({ o.thread.views with vCAP := 0 } : Views) = { c'.views with vCAP := 0 } ∧
      o.mem = c'.mem :=
  let ⟨tree, c', hex, hr, hp, hk, hm, _⟩ := stepOne_runK A hstep ho
  ⟨tree, _, c', hex, hr, hp, hk, hm⟩

/-- Views equal but `vCAP` are `VLe` and forward alike. -/
theorem vle_of_key {V V' : Views} (h : ({ V' with vCAP := 0 } : Views) = { V with vCAP := 0 }) :
    VLe V V' ∧ ∀ l, V'.getFwd l = V.getFwd l := by
  have h1 := congrArg Views.vrNew h
  have h2 := congrArg Views.vrOld h
  have h3 := congrArg Views.vwOld h
  have h4 := congrArg Views.coh h
  have h5 := congrArg Views.fwdb h
  simp only at h1 h2 h3 h4 h5
  refine ⟨⟨Nat.le_of_eq h1.symm, Nat.le_of_eq h2.symm, Nat.le_of_eq h3.symm, fun l => ?_⟩, getFwd_of_fwdb h5⟩
  simp only [Views.getCoh, h4]; exact Nat.le_refl _

/-! ## Memory append

Instances of the existing `Memory.last_append`,
`Memory.get?_append_last`, `Memory.append_time` (`Promising/Rel.lean`) and
`Memory.get?_append_eq_some` (`Promising/Conservative.lean`). -/

theorem last_append (M : Memory) (w : Msg) : (M.append w).1.last = M.last + 1 := Memory.last_append M w

theorem get?_append_new (M : Memory) (w : Msg) : (M.append w).1.get? (M.last + 1) = some w :=
  Memory.get?_append_last M w

theorem append_snd (M : Memory) (w : Msg) : (M.append w).2 = M.last + 1 := Memory.append_time M w

theorem get?_append_cases {M : Memory} {w m : Msg} {ts : Time} (h : (M.append w).1.get? ts = some m) :
    (ts ≤ M.last ∧ M.get? ts = some m) ∨ (ts = M.last + 1 ∧ m = w) :=
  Memory.get?_append_eq_some M w h

/-! ## Other threads' steps and promises -/

variable {i : Nat}

/-- A recorded write is a message of the memory. -/
theorem Facts.rec_le {M : Memory} {V : Views} {g : TkSt} {h : Hist} (hF : Facts x o c i M V g h) {ts : Time}
    (hr : Rec g h ts) : ts ≤ M.last := by
  rcases hr with ⟨hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨hk, rfl⟩
  · exact Memory.last_le_of_get?_eq_some _ (hF.1 1 hk).2.1
  · exact Memory.last_le_of_get?_eq_some _ (hF.1 4 hk).1
  · exact Memory.last_le_of_get?_eq_some _ (hF.1 6 hk).1

/-- The bookkeeping across messages of other threads. -/
theorem Bk.other {M M' : Memory} {P : List Time} {g : TkSt} {h : Hist} (hB : Bk i M P g h) (hp : M.Prefix M')
    (hnew : ∀ ts m, M.last < ts → M'.get? ts = some m → m.tid ≠ i) : Bk i M' P g h := by
  refine ⟨hB.nodup, fun ts hts => ?_, fun ts m hg ht => ?_, hB.recNP⟩
  · obtain ⟨m, hm, hmt⟩ := hB.prom ts hts
    exact ⟨m, get?_prefix hp hm, hmt⟩
  · by_cases hts : ts ≤ M.last
    · exact hB.own ts m (get?_down hp hts hg) ht
    · exact absurd ht (hnew ts m (by omega_t) hg)

/-- **Another thread's step keeps a thread's invariant**: the memory grows
by messages of other threads. -/
theorem JTk.other {M M' : Memory} {V : Views} {P : List Time} {g : TkSt} (hJ : JTk x o c i g V P M)
    (hp : M.Prefix M') (hnew : ∀ ts m, M.last < ts → M'.get? ts = some m → m.tid ≠ i) : JTk x o c i g V P M' :=
  let ⟨h, hF, hB⟩ := hJ
  ⟨h, hF.mono hp (VLe.refl V) rfl rfl, hB.other hp hnew⟩

/-- **The promise step**: the message promised by thread `i`, appended at
`|M| + 1`, is an outstanding promise of the thread; the recorded writes are
older, so none of them is outstanding. -/
theorem Bk.promise {M : Memory} {V : Views} {P : List Time} {g : TkSt} {h : Hist} (hF : Facts x o c i M V g h)
    (hB : Bk i M P g h) (w : Msg) (hw : w.tid = i) : Bk i (M.append w).1 (P ++ [(M.append w).2]) g h := by
  rw [append_snd]
  have hPle : ∀ ts ∈ P, ts ≤ M.last := fun ts hts => by
    obtain ⟨m, hm, -⟩ := hB.prom ts hts; exact Memory.last_le_of_get?_eq_some M hm
  have hn : M.last + 1 ∉ P := fun hm => by have := hPle _ hm; omega_t
  have hp := Memory.Prefix.append M w
  refine ⟨?_, fun ts hts => ?_, fun ts m hg ht => ?_, fun ts hr hin => ?_⟩
  · rw [List.nodup_append]
    exact ⟨hB.nodup, by simp, fun a ha b hb => by
      rw [List.mem_singleton] at hb; subst hb; exact fun e => hn (e ▸ ha)⟩
  · rcases List.mem_append.mp hts with hts | hts
    · obtain ⟨m, hm, hmt⟩ := hB.prom ts hts
      exact ⟨m, get?_prefix hp hm, hmt⟩
    · rw [List.mem_singleton] at hts; subst hts
      exact ⟨w, get?_append_new M w, hw⟩
  · rcases get?_append_cases hg with ⟨-, hg⟩ | ⟨rfl, -⟩
    · exact (hB.own ts m hg ht).imp (fun h => List.mem_append_left _ h) id
    · exact .inl (List.mem_append_right _ (List.mem_singleton_self _))
  · rcases List.mem_append.mp hin with hin | hin
    · exact hB.recNP ts hr hin
    · rw [List.mem_singleton] at hin; have := hF.rec_le hr; omega_t

/-! ## The invariant -/

/-- **The invariant of a configuration**: every message is by one of its
threads, the initial memory is `ini`, and every thread `tid` is in a protocol
state `g` with `Sp tid g` at its ISA state and `JTk x o c tid g`. -/
def Inv (x o c : BitVec 64) (Sp : Nat → TkSt → I.State → Prop) (ini : List (Loc × Val)) (cf : Config I) : Prop :=
  (∀ ts m, cf.mem.get? ts = some m → m.tid < cf.threads.size) ∧ cf.mem.init = ini ∧
    ∀ tid t, cf.threads[tid]? = some t → ∃ g, Sp tid g t.st ∧ JTk x o c tid g t.views t.prom cf.mem

/-- The specification's obligation: every instruction from it runs to a leaf
where it holds again, keeping `JC M0` from every memory `M0`. -/
def StepOK (x o c : BitVec 64) (Sp : Nat → TkSt → I.State → Prop) : Prop :=
  ∀ tid g st tree (M0 : Memory), Sp tid g st → I.exec st = some tree →
    RunOK (E := tk2Env x o c) Arch.tso tid (JC x o c tid M0) (fun s g' => Sp tid g' s) tree g

/-- **One machine step keeps the invariant**: an instruction step (by
`hstep` for the stepping thread, `JTk.other` for the rest) or a promise step
(`Bk.promise` for the promising thread, `JTk.other` for the rest). -/
theorem inv_step [I.LawfulState] {Sp : Nat → TkSt → I.State → Prop} {ini : List (Loc × Val)}
    (hstep : StepOK x o c Sp) {fuel : Nat} {cf cf' : Config I} (hI : Inv x o c Sp ini cf)
    (hs : cf' ∈ (succs Arch.tso cf fuel).1) : Inv x o c Sp ini cf' := by
  obtain ⟨hmsg, hini, hth⟩ := hI
  rcases succ_cases' hs with ⟨j, t, outs, oc, ht, hstep1, ho, rfl⟩ | ⟨j, t, p, ht, -, rfl⟩
  · obtain ⟨tree, iv, c'', hex, hrun, hprom, hkey, hmem⟩ := stepOne_runV Arch.tso hstep1 ho
    obtain ⟨g, hSp, hJ⟩ := hth j t ht
    have hJC : JC x o c j cf.mem g
        { views := t.views, prom := t.prom, mem := cf.mem, log := [.instr j (I.showInstr t.st)] } :=
      ⟨hJ, Memory.Prefix.refl _, fun ts m hlt hg => absurd (Memory.last_le_of_get?_eq_some _ hg) (by omega_t)⟩
    obtain ⟨g', hSp', hJ', hFr⟩ := hstep j g t.st tree cf.mem hSp hex iv _ hJC _ _ hrun
    have hjs := lt_size_of_get? ht
    have hnew : ∀ ts m, cf.mem.last < ts → oc.mem.get? ts = some m → m.tid = j := by
      rw [hmem]; exact hFr.2
    have hp : cf.mem.Prefix oc.mem := hmem ▸ hFr.1
    refine ⟨fun ts m hg => ?_, hp.1.trans hini, fun i t' ht' => ?_⟩
    · show m.tid < (cf.withThread j oc.thread oc.mem).threads.size
      rw [Config.withThread_size]
      by_cases hts : ts ≤ cf.mem.last
      · exact hmsg ts m (get?_down hp hts hg)
      · rw [hnew ts m (by omega_t) hg]; exact hjs
    · rw [Config.withThread_get? _ _ _ hjs] at ht'
      show ∃ g, Sp i g t'.st ∧ JTk x o c i g t'.views t'.prom oc.mem
      split at ht'
      · rename_i hji
        subst hji
        cases ht'
        obtain ⟨h, hF, hB⟩ := hJ'
        obtain ⟨hvle, hfw⟩ := vle_of_key hkey
        refine ⟨g', hSp', h, ?_, ?_⟩
        · rw [hmem]; exact hF.mono (Memory.Prefix.refl _) hvle (hfw _) (hfw _)
        · rw [hmem, hprom]; exact hB
      · rename_i hji
        obtain ⟨gi, hSpi, hJi⟩ := hth i t' ht'
        exact ⟨gi, hSpi, hJi.other hp fun ts m hlt hg => by rw [hnew ts m hlt hg]; exact hji⟩
  · have hjs := lt_size_of_get? ht
    have hp := Memory.Prefix.append cf.mem { p.1 with tid := j }
    refine ⟨fun ts m hg => ?_, hini, fun i t' ht' => ?_⟩
    · show m.tid < (cf.withThread j _ _).threads.size
      rw [Config.withThread_size]
      rcases get?_append_cases hg with ⟨-, hg⟩ | ⟨-, rfl⟩
      · exact hmsg ts m hg
      · exact hjs
    · rw [Config.withThread_get? _ _ _ hjs] at ht'
      show ∃ g, Sp i g t'.st ∧ JTk x o c i g t'.views t'.prom (cf.mem.append { p.1 with tid := j }).1
      split at ht'
      · rename_i hji
        subst hji
        cases ht'
        obtain ⟨g, hSp, h, hF, hB⟩ := hth j t ht
        exact ⟨g, hSp, h, hF.mono hp (VLe.refl _) rfl rfl, hB.promise hF _ rfl⟩
      · rename_i hji
        obtain ⟨gi, hSpi, hJi⟩ := hth i t' ht'
        refine ⟨gi, hSpi, hJi.other hp fun ts m hlt hg => ?_⟩
        rcases get?_append_cases hg with ⟨hle, -⟩ | ⟨-, rfl⟩
        · omega_t
        · exact hji

/-- **The invariant at every reachable configuration.** -/
theorem inv_reachable [I.LawfulState] {Sp : Nat → TkSt → I.State → Prop} {ini : List (Loc × Val)}
    (hstep : StepOK x o c Sp) {fuel : Nat} {c0 cf : Config I} (h0 : Inv x o c Sp ini c0)
    (h : Reachable Arch.tso fuel c0 cf) : Inv x o c Sp ini cf :=
  h.inv (fun _ _ hI hs => inv_step hstep hI hs) h0

/-- **The invariant initially**, from the specification in the start state
at every start state. -/
theorem inv_init {Sp : Nat → TkSt → I.State → Prop} {states : List I.State} {initMem : List (Loc × Val)}
    (h0 : ∀ tid s, states[tid]? = some s → Sp tid TkSt.start s) :
    Inv x o c Sp initMem (Config.init states initMem) := by
  refine ⟨fun ts m hg => by simp [Config.init, Memory.get?] at hg, rfl, fun tid t ht => ?_⟩
  obtain ⟨s, hs, rfl⟩ := Config.init_get?_thread ht
  refine ⟨TkSt.start, h0 tid s hs, ⟨0, 0, 0, 0, 0, 0, 0⟩, ⟨fun n hn => ?_, fun _ => rfl, fun _ => rfl⟩, ?_⟩
  · obtain rfl : n = 0 := by simp [TkSt.start] at hn; omega
    trivial
  · refine ⟨List.nodup_nil, fun ts h => absurd h List.not_mem_nil, fun ts m hg _ => ?_, fun ts hr => ?_⟩
    · simp [Config.init, Memory.get?] at hg
    · simp [Rec, TkSt.start] at hr

end Kraken.Promising.SLR.EnvG.TicketX2

#print axioms Kraken.Promising.SLR.EnvG.TicketX2.Bk.promise
#print axioms Kraken.Promising.SLR.EnvG.TicketX2.inv_reachable
#print axioms Kraken.Promising.SLR.EnvG.TicketX2.inv_init
