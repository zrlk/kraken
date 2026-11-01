/-
**hello.w on AArch64: the pre-spawn segment's end** (`HelloSpawnR.HPreH`;
the twin of `Spike.Lib.WakeHPre.hpre_of` at hello's pre-spawn relation
`HelloO.R1OH … HelloOLift.XH`): at main's clone, from the relation's base
`RSAH` (at `HelloO.IH`) and its source conjuncts (`NoObs`, `VPreH`,
`VPreCH`, `VFlagH`), the clone's `ClonePreH` (`hCl`) and the record the
instance builds at the clone (`hrec`), `tid = 0`, main's spawn as a source
run with the empty trace, and `PreRH`.

- the run: `HelloSpawnLt.run_spawnCfgH` at `ClonePreH`'s packet `p`
  (`SpawnSrcH`) and `NoObs`' `mainExit s = []`;
- `LtPre`: `HelloVPre.vpreH_spawn`; the source coherence `scov0`/`scov1`:
  `HelloVPreC.scovH_of`; the flag: `HelloVFlag.vflagH_spawn` and
  `SpawnFlag.flag_at`;
- the spawned worker's packet `PktH`: `ClonePreH`'s slice words
  (`SlRep`: the buffer's locative, `2`, `13`), `c`'s and main's id words,
  bumped;
- `FrH`: `HPreH`'s extra clone facts at the data `Dd`: main's one source thread and `IH` at the clone (the
  fragment state `hClH_ofR`/`hpc_ofR` consume), from `R1OH`'s base;
- main's source thread past the spawn: at `mTail` with `c` bound
  (`SpawnViewLtSteps.src_fields`), its frames empty by `VPreH`'s stage
  (`HAt` at `spawnTermH` is stage 22, `hfs 22 = []`).

Premises: `hCl` (the clone's `ClonePreH` at the pre-spawn segment's
end), `hrec` (the record at the clone: its spawn record, flag, pointer
words and buffer, and the data's guarantee below the record's; given the
memory relation at the spawn, `c`'s placed word, its label holding a word
and the source memory nonempty, the flag's pre-spawn message; the
buffer's label placed with two words, rodata's messages to it; main's
source thread at the spawn under `VBufR`), `hr0` /
`hr1` (the record's ranges), `hwf` (the layout well formed).
-/
import Spike.Lib.HelloSpawnR
import Spike.Lib.HelloOLift
import Spike.Lib.A64HelloClonePreH
import Spike.Lib.SpawnFlag

namespace Spike.Lib.HelloHPre

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.Handover Spike.Lib.WakeA64 Spike.Lib.Inv2Core Spike.Lib.WakeT1
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.HelloSrc (helloSrc helloS)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloQ (helloQ)
open Spike.Lib.HelloSpawn (SpawnPreH PktH)
open Spike.Lib.HelloSpawnR (PreRH HPreH)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.HelloO (ODataH IH R1OH)
open Spike.Lib.HelloOLift (XH)
open Spike.Lib.HelloMainPreSrc (pktTy spawnTermH SpawnSrcH SlRep)
open Spike.Lib.HelloPreA (ClonePreH)

/-- **`HPreH`'s clone facts at hello's data** (`HelloSpawnR.FrP`; see the module doc): main's one source thread
`th0` and the data's invariant `IH` at main's thread `th`. -/
def FrH (Dd : ODataH) : HelloSpawnR.FrP := fun lbl lsize th s =>
  ∃ (th0 : TermRun.TTh) (hd : Option (Nat × TermRun.Word)), s.ths = #[th0] ∧
    IH Dd lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack

section Inst

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isaLSE2}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : WakeM0.MSide ι} {D : WSideH ι} {r0 r1 : ι → Range}
  {Λ : Scc.Sem.Layout} {asm : String} {E : Entry}

/-- **`HPreH` at hello's pre-spawn relation** (see the module doc). -/
theorem hpre_ofH {μ : Marks} {Dd : ODataH} {r1c : Range}
    /- `R1` is the pre-spawn relation with its source conjuncts -/
    (hR1 : ∀ d s, R1 d s → R1OH arch Λ μ Dd XH d s)
    /- the record's ranges are the data's and the clone's -/
    (hr0 : ∀ w, r0 w = Dd.r0) (hr1 : ∀ w, r1 w = r1c)
    (hwf : Λ.WF)
    /- the clone's facts at the pre-spawn segment's end -/
    (hCl : ∀ d s th stack tls r (th0 : TermRun.TTh) (lbl : WeakMem.AllocLabel → Option Nat)
      (lsize : WeakMem.AllocLabel → Nat) (ts : Nat → Option Nat) (hd : Option (Nat × TermRun.Word)),
      SpawnPrem (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) Λ asm E 0 d s th stack tls r →
      d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
      IH Dd lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      HeldOk2 Λ Dd.r0 Dd.r1 th.st d.2.held → Inv1 Λ lbl lsize ts th d.1.mem s.mem →
      ∃ X : State → Prop, ClonePreH ".L22_wc_main" Λ Dd.r0 r1c X lbl d s)
    /- (the instance) the record at the clone, given the clone's facts:
    the memory relation at the spawn, `c`'s word placed and its label
    holding a word, the source memory nonempty (`WakeOkW.okW_of_clone`'s);
    the buffer's label `lb` placed and holding two words (`BufPl`'s); main's
    source thread at the spawn with the slice's head `lb` and `c`'s label
    `l`, under `VBufR` (where the buffer's and `c`'s labels are fixed); the
    buffer's label off `c`'s -/
    (hrec : ∀ (d : Cfg) (s' : TermRun.Cfg) (lbl : WeakMem.AllocLabel → Option Nat)
      (lsize : WeakMem.AllocLabel → Nat) (l lb : WeakMem.AllocLabel) (cw : TermRun.Word),
      cw.val = .loc ⟨l, 0⟩ 0 → MemInv Dd.G d.1.mem →
      (∃ ts, MemRelP Λ lbl lsize ts d.1.mem s'.mem [] [] []) → (∃ cA, ValRep lbl (.loc ⟨l, 0⟩ 0) cA) →
      0 < lsize l → 0 < s'.mem.size → (∃ b0, lbl lb = some b0) → 2 ≤ lsize lb →
      (∃ (s : TermRun.Cfg) (th0 : TermRun.TTh) (hd : Option (Nat × TermRun.Word)) (ws : List TermRun.Word),
        HelloVBuf.VBufR s ∧ s.ths = #[th0] ∧ SpawnSrcH l ws ⟨th0.term, th0.env, hd⟩ ∧
        ws.head? = some (TermRun.cst (.loc ⟨lb, 0⟩ 0))) →
      ∃ w : ι, SR w = ⟨d.1.mem.last, s'.mem.size, lbl, lsize⟩ ∧ cS w = ⟨l, 0⟩ ∧
        cT w = wordLoc ((lbl l).getD 0 + 8 * 0) ∧ D.cw w = cw ∧ M.cw w = TermRun.cst (.loc ⟨l, 0⟩ 0) ∧
        D.bufL w = lb ∧ D.mB w = 2 ∧ D.nB w = 13 ∧ MemInv (G w) d.1.mem ∧ lb ≠ l)
    /- (the instance; `rfl` at `helloDR`) the worker side's spawn size is
    the record's -/
    (hDS : ∀ w, D.S w = (SR w).S) :
    HPreH arch R1 SR cT cS pT Pa G passT M D r0 r1 Λ asm E (FrH Dd) := by
  intro tid d s th stack tls r hP
  obtain ⟨h1, -, h3, -, -, h6, h7, -⟩ := id hP
  obtain ⟨hRS, hNo, hV, hC, hF, hVB⟩ := hR1 _ _ h1
  rcases hRS with hPre | ⟨_, _, _, _, _, _, _, _, _, _, ⟨_, hk⟩, _⟩
  case inr => rw [hk] at h6; cases h6
  obtain ⟨thm, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E', hKS⟩, -, hH, -, -, hs, hσ, hp0, hJ, -, -, hBnd,
    hInv1, hOwnM, hMemIn, hFits, hMemInv, hOwnOk, -, -, -, -⟩ := hPre
  -- main's thread: `tid = 0`
  have htid : tid = 0 ∧ thm = th := by
    rw [hth] at h3
    rcases tid with _ | n
    · exact ⟨rfl, Option.some.inj h3⟩
    · simp at h3
  obtain ⟨rfl, e⟩ := htid
  subst thm
  have hheld0 : d.2.held = hl := by rw [hKS]; rfl
  obtain ⟨X, hcl⟩ := hCl d s th stack tls r th0 lbl lsize ts hd hP hth hs hσ hp0 hJ (hheld0 ▸ hH) hInv1
  have hclone : ∃ X, ClonePreH ".L22_wc_main" Λ Dd.r0 r1c X lbl d s := ⟨X, hcl⟩
  obtain ⟨thc, th0c, hdc, tlsc, cA, meW, sl0, sl1, sl2, sl3, l, ws, hthc, hsc, -, -, hprom, hcall, -, -, -, -, -,
    -, -, -, hheld, -, -, -, -, -, -, -, -, hSS, htidl, hsl, hvc, -, hfrz⟩ := hcl
  have hSS0 := hSS
  obtain ⟨hterm, -, hc, -, -, hlp⟩ := hSS0
  obtain rfl : thc = th := by
    rw [hth] at hthc; exact (List.singleton_inj.mp (congrArg Array.toList hthc)).symm
  obtain rfl : th0c = th0 := by
    rw [hs] at hsc; exact (List.singleton_inj.mp (congrArg Array.toList hsc)).symm
  simp only at hterm hc hlp
  have h0 : s.ths[0]? = some th0c := by rw [hs]; rfl
  have hsz : s.ths.size = 1 := by rw [hs]; rfl
  -- main's frames are empty at the spawn (stage 22)
  have hstk : th0c.stack = [] := by
    obtain ⟨th', k, wo0, wo1, h0', -, -, hat, -⟩ := hV hsz
    obtain rfl : th' = th0c := by rw [h0] at h0'; exact (Option.some.inj h0').symm
    obtain rfl := HelloVBuf.hat_spawnTerm hat hterm
    exact hat.2.2.2.2.1
  -- the slice's words
  obtain ⟨lb, rfl, hlb, -⟩ := hsl
  -- the run and `LtPre`
  have hex := (WakeNoObs.NoObs.traceOf_nil hNo h6).2
  have hrun := HelloSpawnLt.run_spawnCfgH (arch := arch) h0 hterm hp0 (by rw [hsz]; decide) hlp hex
  obtain ⟨hvl, henv⟩ := HelloVPre.vpreH_spawn hV hsz h0 hterm
  have hths : (TermSpawnStep.spawnCfg s 0 th0c "t" WakeM0.mTail "worker" [] pktTy
      ([TermRun.cst (.loc ⟨lb, 0⟩ 0), TermRun.cst (.num 2), TermRun.cst (.num 13)] ++
        [TermRun.cst (.loc ⟨l, 0⟩ 0), TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])).ths =
      #[TermSpawnStep.spawnPar s 0 th0c "t" WakeM0.mTail,
        TermSpawnStep.spawnKid s 0 th0c "worker" [] pktTy
          ([TermRun.cst (.loc ⟨lb, 0⟩ 0), TermRun.cst (.num 2), TermRun.cst (.num 13)] ++
            [TermRun.cst (.loc ⟨l, 0⟩ 0), TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])] := by
    simp [TermSpawnStep.spawnCfg, TermSpawnStep.spawnT, hs]
  have hsc := HelloVPreC.scovH_of hC hs hp0 rfl hths
  -- the flag
  obtain ⟨i', j', hij, hi, hj, hv⟩ := HelloVFlag.vflagH_spawn hF hs hterm hp0 hc
  obtain ⟨A, hA⟩ : ∃ A, lbl l = some A := by
    obtain ⟨-, x, hx, -⟩ := hvc
    cases h : lbl l with
    | none => simp [wordAddr, h] at hx
    | some A => exact ⟨A, rfl⟩
  obtain ⟨k', hread, hlast⟩ := SpawnFlag.flag_at hInv1 hprom hwf hA hij hi hj hv
  have hcP : TermRun.lookupE (Ctl.of (TermSpawnStep.spawnPar s 0 th0c "t" WakeM0.mTail)).env "c" =
      some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) := by
    simp only [TermRun.evalAt] at hc
    simp [Ctl.of, TermSpawnStep.spawnPar, TermRun.withS, TermRun.lookupE] at hc ⊢
    exact hc
  -- `c`'s label holds a word and the source memory is nonempty: the flag's
  -- message to `⟨l, 0⟩` before the spawn
  have hlsz : 0 < lsize l := by
    obtain ⟨m, hm, hml⟩ := hi
    obtain ⟨-, -, ho⟩ := hInv1.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm))
    rw [hml] at ho
    exact ho
  have hS0 : 0 < s.mem.size := by
    obtain ⟨m, hm, -⟩ := hi
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) (TermLiveProps.lt_of_get hm)
  have hmR : MemRelP Λ lbl lsize ts d.1.mem s.mem [] [] [] := by
    have h := hInv1.mem; rw [hprom] at h; exact h
  -- the buffer's label holds two words: rodata's message to `⟨lb, 1⟩`
  have hlb2 : 2 ≤ lsize lb := by
    obtain ⟨j1, -, ⟨⟨m, hm, hml⟩, -⟩, -⟩ := hfrz lb rfl 1 (by decide)
    obtain ⟨-, -, ho⟩ := hInv1.mem.lbl_mem m (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm))
    rw [hml] at ho
    exact ho
  -- the record
  obtain ⟨w, hSR, hcS, hcT, hcw, hMcw, hbL, hmB, hnB, hGw, hlbl⟩ := hrec d
    (TermSpawnStep.spawnCfg s 0 th0c "t" WakeM0.mTail "worker" [] pktTy
      ([TermRun.cst (.loc ⟨lb, 0⟩ 0), TermRun.cst (.num 2), TermRun.cst (.num 13)] ++
        [TermRun.cst (.loc ⟨l, 0⟩ 0), TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]))
    lbl lsize l lb (TermSpawn.bumpW (TermSpawnStep.spawnS s th0c).vs.vRelSt (TermRun.cst (.loc ⟨l, 0⟩ 0))) rfl
    hMemInv ⟨ts, hmR⟩ ⟨cA, hvc⟩ hlsz hS0 ⟨_, hlb⟩ hlb2 ⟨s, th0c, hdc, _, hVB, hs, hSS, rfl⟩
  -- the published buffer: `ClonePreH`'s rodata messages, their views by `MsgV`
  have hmv : TermViewInv.MsgV s.mem := by
    obtain ⟨_, _, _, _, _, _, _, _, hvi, -⟩ := hV hsz
    exact hvi.1
  have hcwv : (D.cw w).val = .loc ⟨l, 0⟩ 0 := by rw [hcw]; rfl
  have hbuf : HelloW1.BufV (D.bufL w) (D.mB w) (D.S w) (D.cw w)
      (TermSpawnStep.spawnCfg s 0 th0c "t" WakeM0.mTail "worker" [] pktTy
        ([TermRun.cst (.loc ⟨lb, 0⟩ 0), TermRun.cst (.num 2), TermRun.cst (.num 13)] ++
          [TermRun.cst (.loc ⟨l, 0⟩ 0), TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])).mem := by
    rw [hbL, hmB]
    refine HelloW1.bufV_spawn HelloPreA.bufW (by rw [hDS w, hSR]) hmv (fun i _ he => ?_)
      (fun i hi => hfrz lb rfl i hi)
    rw [hcwv] at he
    simp only [WeakMem.Val.loc.injEq, WeakMem.Address.mk.injEq] at he
    exact hlbl he.1.1.symm
  refine ⟨rfl, _, w, TermSpawnStep.spawnPar s 0 th0c "t" WakeM0.mTail,
    TermSpawnStep.spawnKid s 0 th0c "worker" [] pktTy
      ([TermRun.cst (.loc ⟨lb, 0⟩ 0), TermRun.cst (.num 2), TermRun.cst (.num 13)] ++
        [TermRun.cst (.loc ⟨l, 0⟩ 0), TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]),
    lbl, lsize, ts, k', Dd.own thc.st th0c.stack, l, hrun, ?_, (by unfold FrH; exact ⟨th0c, hd, hs, hJ⟩)⟩
  exact {
    pre := {
      SR := hSR
      threads := hth
      ths := hths
      inv1 := hInv1
      prom := hprom
      msgs := hOwnM
      memIn := hMemIn
      fits := hFits
      memInv := hGw
      bnd := hBnd
      own := hOwnOk
      sp0 := hp0
      sp1 := rfl
      scov0 := fun k m hm _ => hsc.1 k m hm
      scov1 := fun k m hm _ => hsc.2 k m hm
      flag := by show d.1.mem.read? (cT w) k' = some 0; rw [hcT]; exact hread
      flagLast := by show ∀ k w', k' < k → d.1.mem.get? k = some w' → w'.loc ≠ cT w; rw [hcT]; exact hlast
      st1 := rfl
      σ1 := rfl
      term1 := rfl
      env1 := ⟨pktTy, TermSpawn.bumpW (TermSpawnStep.spawnS s th0c).vs.vRelSt (TermRun.cst (.loc ⟨lb, 0⟩ 0)),
        TermSpawn.bumpW (TermSpawnStep.spawnS s th0c).vs.vRelSt (TermRun.cst (.num 2)),
        TermSpawn.bumpW (TermSpawnStep.spawnS s th0c).vs.vRelSt (TermRun.cst (.num 13)),
        TermSpawn.bumpW (TermSpawnStep.spawnS s th0c).vs.vRelSt (TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)),
        by simp [TermSpawnStep.spawnKid, hcw], rfl, by rw [hbL]; rfl, by rw [hmB]; rfl,
        by rw [hmB]; decide, by rw [hnB]; rfl⟩
      buf := hbuf
      slots := ⟨j, by rw [hKS]; rfl⟩
      held := by rw [hheld, hr1, hr0]
      top := by
        rw [h7] at hcall
        simp only [Option.some.injEq, Scc.Sem.Kernel.Call.clone.injEq] at hcall
        rw [hr1]; exact hcall.1.symm
      live := fun s0' h => by
        rw [hths] at h
        obtain rfl := Option.some.inj h
        simp [TermSpawnStep.spawnPar, WakeM0.mTail, WakeMLive.wlRet]
      trace := HelloNoObs.NoObs.run_nilH hNo hrun h6 }
    hcS := hcS
    stack0 := hstk
    σ0 := hσ
    term0 := .inl rfl
    env0 := ⟨_, _, _, by rw [hMcw]; exact hcP, rfl, rfl⟩
    prom0 := hp0
    tid0 := by show th0c.tidLbl.orElse _ = _; rw [htidl]; rfl
    hlt := ⟨pktTy, th0c, _, _, _, _, _, hs, rfl, hvl ⟨l, 0⟩,
      fun x hx => henv _ (TermNoFul.lookupE_mem (env := th0c.env) (x := "p") hlp) x hx⟩
    clone := by rw [hr0, hr1]; exact hclone
    hsp := ⟨th0c, _, hs, hc, rfl⟩
    hcT := hcT
    hlsz := hlsz }

end Inst

/-- info: 'Spike.Lib.HelloHPre.hpre_ofH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hpre_ofH

end Spike.Lib.HelloHPre
