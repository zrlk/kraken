/-
Dead promises: a promise at or below the thread's `vwNew` can never be
fulfilled, so a thread holding one is not certifiable.

Kraken's `writeOk t` asks `max writePre (coh l) < t`, and `writePre`
includes `vwNew`; `vwNew` only grows along a run (`Ctx.WOrd`,
`runTree_word`). So once `p ≤ vwNew` with `p` outstanding, `p` stays
outstanding forever and the thread can never reach `prom = []`.

Use for the allocator (DESIGN §9.0, "Fresh allocation"): the cursor RMW
of `allocF` is emitted as `ldaddal` (A64) / `lock xadd` (x64), and Kraken's
`rmwPost` raises `vwNew` to the RMW's write timestamp `q` for `acqRel`. By
`certOkC_prom_gt_vwNew` a certifiable thread then holds no promise at or
below `q`. When the RMW appends, `q` is above every message, so the thread
holds no promise at all; when it fulfils an earlier promise `q` of its own,
promises above `q` survive.

- `Ctx.DeadAt`: `p` outstanding and `p ≤ vwNew`.
- `runTree_deadAt`, `stepOneWith_deadAt`, `threadNPC_deadAt`: the property
  survives a context run, an instruction and a solo run.
- `not_certOkC_of_dead`: a thread with a dead promise is not certifiable.
- `certOkC_prom_gt_vwNew`: in a certifiable thread every promise lies above
  `vwNew`.
-/
import Scc.Sem.Ext
import Kraken.Promising.AcqFloor

namespace Scc.Sem

open Kraken Kraken.Promising

/-- Promise `p` is outstanding in `c` and at or below its `vwNew`, so no
write can fulfil it any more. -/
def Ctx.DeadAt (p : Time) (c : Ctx) : Prop :=
  p ∈ c.prom ∧ p ≤ c.views.vwNew

/-- `DeadAt` is preserved along any `WOrd` step: `vwNew` only grows, and a
promise removed in between was above the old `vwNew`. -/
theorem Ctx.DeadAt.of_wOrd {p : Time} {c c' : Ctx} (hw : c.WOrd c') (h : Ctx.DeadAt p c) :
    Ctx.DeadAt p c' := by
  obtain ⟨hm, hle⟩ := h
  by_cases hm' : p ∈ c'.prom
  · exact ⟨hm', Nat.le_trans hle hw.vwNew⟩
  · exact absurd (hw.prom p hm hm') (Nat.not_lt.mpr hle)

/-- **A run of an event tree keeps a dead promise dead.** -/
theorem runTree_deadAt (A : Arch) (tid : Nat) (iv : InstrViews) {σ : Type} (tree : EvTree σ)
    {p : Time} {c : Ctx} {s : σ} {c' : Ctx} (hr : .ok (s, c') ∈ runTree A tid iv c tree)
    (h : Ctx.DeadAt p c) : Ctx.DeadAt p c' :=
  h.of_wOrd (runTree_word A tid iv tree c s c' hr)

/-- **One instruction under `cexec` keeps a dead promise dead.** -/
theorem stepOneWith_deadAt {I : ISA} (A : Arch) {cs : CertSem I}
    {t : Thread I} {tid : Nat} {mem : Memory} {outs : List (Except String (Kraken.Promising.Outcome I))}
    (hstep : cs.step A t tid mem = some outs) {o : Kraken.Promising.Outcome I}
    (ho : .ok o ∈ outs) {p : Time} (h : p ∈ t.prom ∧ p ≤ t.views.vwNew) :
    p ∈ o.thread.prom ∧ p ≤ o.thread.views.vwNew := by
  unfold CertSem.step stepOneWithD at hstep
  cases hex : cs.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok q =>
      obtain ⟨st, c'⟩ := q
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      have hd := runTree_deadAt A tid _ tree hr h
      obtain ⟨e1, e2⟩ := finishInstr_relKey hth
      have e3 : th.views.vwNew = c'.views.vwNew := by have := congrArg Views.vwNew e2; exact this
      exact ⟨e1 ▸ hd.1, e3 ▸ hd.2⟩

/-- **A solo run keeps a dead promise dead.** -/
theorem threadNPC_deadAt {I : ISA} (A : Arch) {cs : CertSem I} {tid : Nat}
    {x y : Thread I × Memory} (hr : ThreadNPC A cs tid x y) {p : Time}
    (h : p ∈ x.1.prom ∧ p ≤ x.1.views.vwNew) : p ∈ y.1.prom ∧ p ≤ y.1.views.vwNew := by
  induction hr with
  | refl => exact h
  | step hs _ ih =>
    obtain ⟨outs, o, hso, ho, rfl⟩ := hs
    exact ih (stepOneWith_deadAt A hso ho h)

/-- **A thread holding a dead promise is not certifiable**: a promise at or
below `vwNew` stays outstanding along every solo run, which therefore never
reaches `prom = []`. -/
theorem not_certOkC_of_dead {I : ISA} (A : Arch) (cs : CertSem I) (tid : Nat)
    {t : Thread I} {mem : Memory} {p : Time} (hp : p ∈ t.prom) (hle : p ≤ t.views.vwNew) :
    ¬ CertOkC A cs tid t mem := by
  rintro ⟨t', mem', hr, he⟩
  have := (threadNPC_deadAt A hr (x := (t, mem)) ⟨hp, hle⟩).1
  rw [he] at this; cases this

/-- **Every promise of a certifiable thread lies above its `vwNew`.** In
particular, right after an acquire-release RMW (which raises `vwNew` to its
write timestamp) a certifiable thread holds no promise at or below that
timestamp. -/
theorem certOkC_prom_gt_vwNew {I : ISA} {A : Arch} {cs : CertSem I} {tid : Nat}
    {t : Thread I} {mem : Memory} (hc : CertOkC A cs tid t mem) {p : Time} (hp : p ∈ t.prom) :
    t.views.vwNew < p :=
  Nat.lt_of_not_le fun hle => not_certOkC_of_dead A cs tid hp hle hc

end Scc.Sem
