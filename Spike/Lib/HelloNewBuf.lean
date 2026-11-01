/-
**hello.w: rodata's buffer label at main's `spawn`** (B8 row 4c's source
half; `HelloOkW`'s `lBH` and `BufPl`'s `lB ≠ cS.label`): along source runs
from the start (`HelloVBuf.VBufR`, main's stage `HAt`), the buffer's label
the slice carries to the `spawn` is main's first allocation after its
`ThreadId` box, `freshLabel 0 2 0 1` (`HelloOkW.lBH`), and the box's label
`c` carries is main's second, `freshLabel 0 2 0 2` (`HelloPreTerm.lbX`):
no other allocation happens from the start to rodata's `newBuf` (`HAt`'s
allocation count `hna`, `NewBufE` at label `lbB`).

- `clonePreH_labels`: the same at `ClonePreH`'s source side (`lb ≠ l` too).
- `rodata_newBuf_label`: at `spawnTermH` (`SpawnSrcH l ws`), under `VBufR`
  with main the only thread, the slice's buffer label is `lBH` and `c`'s
  label is `lbX`; so the two differ (`lBH_ne_box`).
- **Not vacuous**: `stepN`, a deterministic run of thread 0 on
  `helloSrc` (a run of `helloS arch` with the empty trace, `runN_run`),
  takes 22 steps from `setupStartT 2` (`stepN_some`, kernel evaluation) to
  `sSp arch`: main alone, promise-free, 3 allocations, 8 bindings
  (`sSp_shape`, kernel evaluation). There `VBufR` holds (`vbufR_init`,
  `vbufR_run`), its stage is 22, and so `rodata_newBuf_label`'s premises
  hold (`reach_spawn`; the `example` applies it).
-/
import Spike.Lib.HelloVBuf
import Spike.Lib.HelloOkW

namespace Spike.Lib.HelloNewBuf

open CoreLang CoreTerm TermRun
open Scc.Sem Scc.Sem.SrcSem
open Spike.Lib.HelloSrc (helloSrc helloS)
open Spike.Lib.HelloMainPreSrc
open Spike.Lib.HelloPreTerm
open Spike.Lib.HelloVBuf (VBufR vbufR_init vbufR_run)
open Spike.Lib.HelloOkW (lBH)

/-! ## The labels at the `spawn` -/

/-- **Rodata's buffer label at main's `spawn`**: along source runs
(`VBufR`), with main the only thread at `spawnTermH` (`SpawnSrcH l ws`),
the slice's buffer label `lb` is main's first allocation after its
`ThreadId` box (`lBH`) and `c`'s label `l` its second (`lbX`). -/
theorem rodata_newBuf_label {s : Cfg} {th0 : TTh} {l : WeakMem.AllocLabel} {ws : List Word}
    {lb : WeakMem.AllocLabel} {hd : Option (Nat × Word)} (hv : VBufR s) (hs : s.ths = #[th0])
    (hS : SpawnSrcH l ws ⟨th0.term, th0.env, hd⟩) (hh : ws.head? = some (cst (.loc ⟨lb, 0⟩ 0))) :
    lb = lBH ∧ l = lbX := by
  obtain ⟨th, k, wo0, wo1, h0, -, -, hat, -⟩ := hv (by rw [hs]; rfl)
  rw [hs] at h0
  obtain rfl : th0 = th := by simpa using h0
  obtain rfl := HelloVBuf.hat_spawnTerm hat hS.1
  have hsl := hS.2.2.2.2.1
  have hcc := hS.2.2.1
  change evalAt th0.env (.var "sl") = some (slTy, ws) at hsl
  change evalAt th0.env (.var "c") = some (.ptr .pub .int, [cst (.loc ⟨l, 0⟩ 0)]) at hcc
  rw [hat.2.2.1] at hsl hcc
  simp [hc, envP0, envC, envO, c0H, envS, evalAt, lookupE] at hsl
  simp [hc, envP0, envC, envO, evalAt, lookupE, cst, Promises.TVal.mk0] at hcc
  subst hsl
  simp [cst, Promises.TVal.mk0] at hh
  exact ⟨hh.symm, hcc.symm⟩

/-- The buffer's label is not the box's (`BufPl`'s `lB ≠ cS.label` at the
`spawn`'s `c`). -/
theorem lBH_ne_box : lBH ≠ lbX := by decide

/-- **At the clone** (`ClonePreH`'s source side, `ClonePreH.src`): under
`VBufR`, the slice's buffer label `lb` (`SlRep`'s, placed at `x9`) is `lBH`
and `c`'s label `l` (placed at `x13`) is `lbX`; so `lb ≠ l`. -/
theorem clonePreH_labels {pfx : String} {Λ : Scc.Sem.Layout} {r0 r1 : Range}
    {X : Kraken.Promising.AArch64.State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {t : Spike.Lib.WakeA64.Cfg} {s : Cfg} (hv : VBufR s) (h : HelloPreA.ClonePreH pfx Λ r0 r1 X lbl t s) :
    ∃ (th0 : TTh) (hd : Option (Nat × Word)) (l lb : WeakMem.AllocLabel) (ws : List Word),
      s.ths = #[th0] ∧ SpawnSrcH l ws ⟨th0.term, th0.env, hd⟩ ∧ ws.head? = some (cst (.loc ⟨lb, 0⟩ 0)) ∧
      lb = lBH ∧ l = lbX ∧ lb ≠ l := by
  obtain ⟨_, th0, hd, l, ws, _, hs, hS, _, hR, _, _⟩ := h.src
  obtain ⟨lb, rfl, -⟩ := hR
  obtain ⟨h1, h2⟩ := rodata_newBuf_label hv hs hS rfl
  exact ⟨th0, hd, l, lb, _, hs, hS, rfl, h1, h2, by rw [h1, h2]; exact lBH_ne_box⟩

/-! ## Not vacuous: hello's own run reaches the `spawn` -/

/-- Thread `0`'s deterministic run on `helloSrc`: `n` steps, each the
unique thread step (`none` otherwise). -/
def stepN (arch : WeakMem.Arch) : Nat → Cfg → Option Cfg
  | 0, c => some c
  | n + 1, c =>
    match threadSteps helloSrc Promises.Knobs.all arch c 0 with
    | [c'] => if noPromises c' 0 = true ∧ mainExit c = [] ∧
        (srcObs traceOf c').length ≤ (srcObs traceOf c).length then stepN arch n c' else none
    | _ => none

/-- **A run of `stepN` is a run of `helloS`** with the empty trace. -/
theorem runN_run {arch : WeakMem.Arch} : ∀ {n : Nat} {c c' : Cfg}, stepN arch n c = some c' →
    (helloS arch).Run c [] c'
  | 0, c, c', h => by cases h; exact .refl _
  | n + 1, c, c', h => by
    unfold stepN at h
    split at h
    · rename_i c1 hst
      split at h
      · rename_i hc
        obtain ⟨hp, hm, ht⟩ := hc
        have hstep : (helloS arch).step 0 c [] c1 := by
          have hmem : c1 ∈ threadSteps helloSrc Promises.Knobs.all arch c 0 := by
            rw [hst]; exact List.mem_singleton_self _
          refine ⟨hm, .inl (.inl ⟨hmem, c1, .refl _, hp⟩), ?_⟩
          exact (List.drop_eq_nil_of_le ht).symm
        exact .step (es := []) (tr := []) ⟨0, hstep⟩ (runN_run h)
      · simp at h
    · simp at h

/-- `stepN` runs `22` steps from the start (kernel evaluation). -/
theorem stepN_some (arch : WeakMem.Arch) : (stepN arch 22 (Spike.Lib.WakeT1.setupStartT 2)).isSome = true := by
  cases arch <;> decide +kernel

/-- **hello's spawn configuration**: the start after `22` steps of main. -/
def sSp (arch : WeakMem.Arch) : Cfg := (stepN arch 22 (Spike.Lib.WakeT1.setupStartT 2)).get (stepN_some arch)

/-- Its decidable shape: main alone, promise-free, three allocations made,
eight bindings (kernel evaluation). -/
theorem sSp_shape (arch : WeakMem.Arch) : (sSp arch).ths.size = 1 ∧ (sSp arch).ths[0]?.map (·.promises) = some [] ∧
    (sSp arch).ths[0]?.map (·.nalloc) = some 3 ∧ (sSp arch).ths[0]?.map (·.env.length) = some 8 := by
  cases arch <;> decide +kernel

/-- `sSp` is reached from the start with the empty trace. -/
theorem sSp_reach (arch : WeakMem.Arch) : (helloS arch).Run (Spike.Lib.WakeT1.setupStartT 2) [] (sSp arch) :=
  runN_run (Option.some_get (stepN_some arch)).symm

theorem hna_ge {k : Nat} (h : hna k = 3) : 19 ≤ k := by
  unfold hna at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · omega

/-- **Not vacuous**: hello's own run reaches main at the `spawn` (`VBufR`,
main alone and promise-free, `SpawnSrcH` at the box's label and the slice
`slW`, whose head is the buffer's locative): `rodata_newBuf_label`'s
premises hold there. -/
theorem reach_spawn (arch : WeakMem.Arch) : ∃ s th0, (helloS arch).Run (Spike.Lib.WakeT1.setupStartT 2) [] s ∧
    VBufR s ∧ s.ths = #[th0] ∧ th0.promises = [] ∧ SpawnSrcH lbX slW ⟨th0.term, th0.env, none⟩ ∧
    slW.head? = some (cst (.loc ⟨lBH, 0⟩ 0)) := by
  obtain ⟨h1, hp, hn, hl⟩ := sSp_shape arch
  have hv := vbufR_run (sSp_reach arch) (vbufR_init (s := Spike.Lib.WakeT1.setupStartT 2) (arch := arch)
    (by change Spike.Lib.WakeT1.progInitT helloSrc 2 _; rw [Spike.Lib.HelloSrc.hello_start]))
  obtain ⟨th, k, wo0, wo1, h0, -, -, hat, -⟩ := hv h1
  have hs : (sSp arch).ths = #[th] := by
    apply Array.ext (by simp [h1])
    intro i hi _
    obtain rfl : i = 0 := by omega
    simpa [Array.getElem?_eq_getElem hi] using h0
  rw [h0] at hp hn hl
  simp only [Option.map_some, Option.some.injEq] at hp hn hl
  obtain ⟨hk, ht, he, -, -, hna'⟩ := hat
  have h19 := hna_ge (hna'.symm.trans hn)
  obtain rfl : k = 22 := by
    rw [he] at hl
    match k, hk, h19 with
    | 19, _, _ | 20, _, _ | 21, _, _ => simp [hc, envO, envC, envP0, c0H, envS] at hl
    | 22, _, _ => rfl
    | _ + 23, hk, _ => omega
  refine ⟨sSp arch, th, sSp_reach arch, hv, hs, hp, ⟨ht, rfl, ?_, ?_, ?_, ?_⟩, rfl⟩ <;>
    simp [he, hc, envP0, envC, envO, c0H, envS, evalAt, lookupE, slW, meW]

/-- `rodata_newBuf_label` applies on hello's own run. -/
example (arch : WeakMem.Arch) : ∃ s th0, (helloS arch).Run (Spike.Lib.WakeT1.setupStartT 2) [] s ∧
    s.ths = #[th0] ∧ th0.promises = [] := by
  obtain ⟨s, th0, hr, hv, hs, hp, hS, hh⟩ := reach_spawn arch
  obtain ⟨-, -⟩ := rodata_newBuf_label hv hs hS hh
  exact ⟨s, th0, hr, hs, hp⟩

/-- info: 'Spike.Lib.HelloNewBuf.rodata_newBuf_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rodata_newBuf_label

/-- info: 'Spike.Lib.HelloNewBuf.reach_spawn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reach_spawn

end Spike.Lib.HelloNewBuf
