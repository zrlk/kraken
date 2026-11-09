/-
**hello.w on x86-64: the pre-spawn segment's end** (`X64HelloSpawnR.HPreH`;
the twin of `Spike.Lib.HelloHPre`, at hello's x86-64 pre-spawn relation
`X64HelloO.R1OH … X64HelloOLift.XH`): at main's clone, from the relation's base
`RSAH` (at `X64HelloO.IH`) and its source conjuncts (`NoObs`, `VPreH`,
`VPreCH`, `VFlagH`), the clone's `ClonePreH` (`hCl`) and the record the
instance builds at the clone (`hrec`), `tid = 0`, main's spawn as a source
run with the empty trace, and `PreRH`.

- `FrH`: `HPreH`'s extra clone facts at the data `Dd`: main's one source
  thread and `IH` at the clone.
- `wakeOwnXW_inj_at`, `wakeOwnXW_inj`: `X64WakeOwnX.wakeOwnXW T W` determines `T` and `W`;
  `ne_wakeOwnXW_of_nil`: an own map with no thread 0 word at a record and state is not of that form.
- `hpre_ofH`: `HPreH` at hello's pre-spawn relation. The proof is
  `HelloHPre.hpre_ofH`'s, step for step: the run
  `X64HelloSpawnLt.run_spawnCfgH`, `LtPre` `X64HelloVPre.vpreH_spawn`, the
  source coherence `X64HelloVPreC.scovH_of`, the flag
  `X64HelloVFlag.vflagH_spawn` and `X64SpawnFlag.flag_at`, the buffer
  `X64HelloW1.bufV_spawn`.

Premises: as AArch64's (`hCl`, `hrec`, `hr0`/`hr1`, `hwf`, `hDS`), and `hself` for `SpawnPreH.self`.

**Where this differs from AArch64** (forced by the x86-64 shape):
- `asm : Scc.Sem.X64.Asm` and `isa` (AArch64: `String`, `isaLSE2`).
- `hCl` concludes `X64HelloPreA.ClonePreH Λ Dd.r0 r1c X lbl d s`. There is no
  label prefix: x86-64's `cloneAtH` takes none (AArch64: `ClonePreH ".L22_wc_main" …`).
  Its buffer conjunct is `X64HelloInst.BufAtSpawn`, and `hlb2`/`hbuf` apply it as before.
- `pktTy` comes from `X64HelloSplit`, and `bufW` from `X64HelloInst`.
- `SpawnPreH` has the field `self` (both TCB self words at the clone; AArch64 has no TCB word). Its premise
  `hself` applies only when the relation's own map is `wakeOwnXW T W`: then `T`, `W` are the layout `L`'s
  `tcbM L`, `tcbWH L`, the layout is `L`'s, the data's own map is `ownGHXW L a` and main's thread at the clone is
  on `L`'s executable. The field is `X64HelloSelfClone`'s `selfWords_clone` at `ClonePreH`'s pc, stack and
  `Owned` facts, from the relation's `OwnOk`. `hself` reads the own map at one record and state, so while
  main's own map is empty it holds by `ne_wakeOwnXW_of_nil` (an `ι`-wide equation would not be refutable at
  an empty record type).
-/
import Spike.Lib.X64HelloSpawnR
import Spike.Lib.X64HelloOLift
import Spike.Lib.X64HelloClonePreH
import Spike.Lib.X64SpawnFlag
import Spike.Lib.X64HelloSelfClone

namespace Spike.Lib.X64HelloHPre

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.Handover Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core Spike.Lib.X64WakeT1
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64HelloSrc (helloSrc helloS)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloQ (helloQ)
open Spike.Lib.X64HelloSpawn (SpawnPreH PktH)
open Spike.Lib.X64HelloSpawnR (PreRH HPreH)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64HelloO (ODataH IH R1OH)
open Spike.Lib.X64HelloOLift (XH)
open Spike.Lib.X64HelloMainPreSrc (spawnTermH SpawnSrcH SlRep)
open Spike.Lib.X64HelloSplit (pktTy)
open Spike.Lib.X64HelloPreA (ClonePreH)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh (tcbM)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Spike.Lib.X64.HelloPh (ownGHXW)
open Spike.Lib.X64WakeOwnX (wakeOwnXW)
open SccCode (helloCells)

/-- **`wakeOwnXW T W` determines `T` and `W`** at one record and state (thread 0's word is `T`'s, thread 1's
`W`'s). -/
theorem wakeOwnXW_inj_at {ι : Type} {w : ι} {s : isa.State} {T W T' W' : BitVec 64}
    (h : ∀ i, wakeOwnXW T W w i s [] = wakeOwnXW T' W' w i s []) : T = T' ∧ W = W' := by
  have h0 := h 0
  have h1 := h 1
  simp only [X64WakeOwnX.wakeOwnXW_zero, X64WakeOwnX.wakeOwnXW_one, List.cons.injEq, Prod.mk.injEq,
    Loc.mk.injEq] at h0 h1
  exact ⟨h0.1.1.1, h1.1.1.1⟩

/-- **`wakeOwnXW T W` determines `T` and `W`** (given a record and a state). -/
theorem wakeOwnXW_inj {ι : Type} (w : ι) (s : isa.State) {T W T' W' : BitVec 64}
    (h : (wakeOwnXW T W : ι → Nat → isa.State → List TermRun.Frame → List (Loc × Val)) = wakeOwnXW T' W') :
    T = T' ∧ W = W' :=
  wakeOwnXW_inj_at (w := w) (s := s) fun i => by rw [h]

/-- **An empty word list is not `wakeOwnXW T W`'s thread 0 words** at any record and state (thread 0 owns `T`
there): an own map whose thread 0 words are empty at one record and state is not `wakeOwnXW T W`. -/
theorem ne_wakeOwnXW_of_nil {ι : Type} {o : List (Loc × Val)} (h : o = []) (w : ι) (s : isa.State)
    (T W : BitVec 64) : o ≠ wakeOwnXW T W w 0 s [] := by
  rw [h]; simp

/-- **`HPreH`'s clone facts at hello's data** (`X64HelloSpawnR.FrP`; see the module doc): main's one source thread
`th0` and the data's invariant `IH` at main's thread `th`. -/
def FrH (Dd : ODataH) : X64HelloSpawnR.FrP := fun lbl lsize th s =>
  ∃ (th0 : TermRun.TTh) (hd : Option (Nat × TermRun.Word)), s.ths = #[th0] ∧
    IH Dd lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack

section Inst

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isa}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : X64WakeM0.MSide ι} {D : WSideH ι} {r0 r1 : ι → Range}
  {Λ : Scc.Sem.Layout} {asm : Scc.Sem.X64.Asm} {E : Entry}

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
      ∃ X : State → Prop, ClonePreH Λ Dd.r0 r1c X lbl d s)
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
        X64HelloVBuf.VBufR s ∧ s.ths = #[th0] ∧ SpawnSrcH l ws ⟨th0.term, th0.env, hd⟩ ∧
        ws.head? = some (TermRun.cst (.loc ⟨lb, 0⟩ 0))) →
      ∃ w : ι, SR w = ⟨d.1.mem.last, s'.mem.size, lbl, lsize⟩ ∧ cS w = ⟨l, 0⟩ ∧
        cT w = wordLoc ((lbl l).getD 0 + 8 * 0) ∧ D.cw w = cw ∧ M.cw w = TermRun.cst (.loc ⟨l, 0⟩ 0) ∧
        D.bufL w = lb ∧ D.mB w = 2 ∧ D.nB w = 13 ∧ MemInv (G w) d.1.mem ∧ lb ≠ l)
    /- (the instance; `rfl` at `helloDR`) the worker side's spawn size is
    the record's -/
    (hDS : ∀ w, D.S w = (SR w).S)
    /- (`SpawnPreH.self`) when the relation's own map is `wakeOwnXW T W` at a record and a state: the words
    are `L`'s TCB self words, the layout is `L`'s with the hello cells' labels, the data's own map is
    `ownGHXW L a`, and main's thread at the clone is on `L`'s executable -/
    {L : RuntimeLayout} {a : BitVec 64}
    (hself : ∀ (w : ι) (st : isa.State) T W,
      (∀ i, (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1).own w i st [] = wakeOwnXW T W w i st []) →
      T = tcbM L ∧ W = tcbWH L ∧ Λ = L.Λ ∧
      (∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x → L.lab l = Int64.ofNat x) ∧
      (∀ s fs, Dd.own s fs = ownGHXW L a s) ∧
      ∀ d s th stack tls r, SpawnPrem (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) Λ asm E 0 d s th stack tls r →
        th.st.exe = L.exe) :
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
  have hclone : ∃ X, ClonePreH Λ Dd.r0 r1c X lbl d s := ⟨X, hcl⟩
  obtain ⟨thc, th0c, hdc, tlsc, cA, meW, sl0, sl1, sl2, sl3, l, ws, hthc, hsc, hpcC, -, hprom, hcall, -, -, -, -,
    -, -, -, -, hheld, -, hO, -, -, -, -, htop, hr0sz, hSS, htidl, hsl, hvc, -, hfrz⟩ := hcl
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
    obtain rfl := X64HelloVBuf.hat_spawnTerm hat hterm
    exact hat.2.2.2.2.1
  -- the slice's words
  obtain ⟨lb, rfl, hlb, -⟩ := hsl
  -- the run and `LtPre`
  have hex := (X64WakeNoObs.NoObs.traceOf_nil hNo h6).2
  have hrun := X64HelloSpawnLt.run_spawnCfgH (arch := arch) h0 hterm hp0 (by rw [hsz]; decide) hlp hex
  obtain ⟨hvl, henv⟩ := X64HelloVPre.vpreH_spawn hV hsz h0 hterm
  have hths : (TermSpawnStep.spawnCfg s 0 th0c "t" X64WakeM0.mTail "worker" [] pktTy
      ([TermRun.cst (.loc ⟨lb, 0⟩ 0), TermRun.cst (.num 2), TermRun.cst (.num 13)] ++
        [TermRun.cst (.loc ⟨l, 0⟩ 0), TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])).ths =
      #[TermSpawnStep.spawnPar s 0 th0c "t" X64WakeM0.mTail,
        TermSpawnStep.spawnKid s 0 th0c "worker" [] pktTy
          ([TermRun.cst (.loc ⟨lb, 0⟩ 0), TermRun.cst (.num 2), TermRun.cst (.num 13)] ++
            [TermRun.cst (.loc ⟨l, 0⟩ 0), TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])] := by
    simp [TermSpawnStep.spawnCfg, TermSpawnStep.spawnT, hs]
  have hsc := X64HelloVPreC.scovH_of hC hs hp0 rfl hths
  -- the flag
  obtain ⟨i', j', hij, hi, hj, hv⟩ := X64HelloVFlag.vflagH_spawn hF hs hterm hp0 hc
  obtain ⟨A, hA⟩ : ∃ A, lbl l = some A := by
    obtain ⟨-, x, hx, -⟩ := hvc
    cases h : lbl l with
    | none => simp [wordAddr, h] at hx
    | some A => exact ⟨A, rfl⟩
  obtain ⟨k', hread, hlast⟩ := X64SpawnFlag.flag_at hInv1 hprom hwf hA hij hi hj hv
  have hcP : TermRun.lookupE (Ctl.of (TermSpawnStep.spawnPar s 0 th0c "t" X64WakeM0.mTail)).env "c" =
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
    (TermSpawnStep.spawnCfg s 0 th0c "t" X64WakeM0.mTail "worker" [] pktTy
      ([TermRun.cst (.loc ⟨lb, 0⟩ 0), TermRun.cst (.num 2), TermRun.cst (.num 13)] ++
        [TermRun.cst (.loc ⟨l, 0⟩ 0), TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]))
    lbl lsize l lb (TermSpawn.bumpW (TermSpawnStep.spawnS s th0c).vs.vRelSt (TermRun.cst (.loc ⟨l, 0⟩ 0))) rfl
    hMemInv ⟨ts, hmR⟩ ⟨cA, hvc⟩ hlsz hS0 ⟨_, hlb⟩ hlb2 ⟨s, th0c, hdc, _, hVB, hs, hSS, rfl⟩
  -- the published buffer: `ClonePreH`'s rodata messages, their views by `MsgV`
  have hmv : TermViewInv.MsgV s.mem := by
    obtain ⟨_, _, _, _, _, _, _, _, hvi, -⟩ := hV hsz
    exact hvi.1
  have hcwv : (D.cw w).val = .loc ⟨l, 0⟩ 0 := by rw [hcw]; rfl
  have hbuf : X64HelloW1.BufV (D.bufL w) (D.mB w) (D.S w) (D.cw w)
      (TermSpawnStep.spawnCfg s 0 th0c "t" X64WakeM0.mTail "worker" [] pktTy
        ([TermRun.cst (.loc ⟨lb, 0⟩ 0), TermRun.cst (.num 2), TermRun.cst (.num 13)] ++
          [TermRun.cst (.loc ⟨l, 0⟩ 0), TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])).mem := by
    rw [hbL, hmB]
    refine X64HelloW1.bufV_spawn X64HelloInst.bufW (by rw [hDS w, hSR]) hmv (fun i _ he => ?_)
      (fun i hi => hfrz lb rfl i hi)
    rw [hcwv] at he
    simp only [WeakMem.Val.loc.injEq, WeakMem.Address.mk.injEq] at he
    exact hlbl he.1.1.symm
  refine ⟨rfl, _, w, TermSpawnStep.spawnPar s 0 th0c "t" X64WakeM0.mTail,
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
        simp [TermSpawnStep.spawnPar, X64WakeM0.mTail, WakeMLive.wlRet]
      trace := X64HelloNoObs.NoObs.run_nilH hNo hrun h6
      self := fun T W hQ => by
        obtain ⟨rfl, rfl, rfl, hlab, hDo, hexe⟩ := hself w thc.st T W fun i => by rw [hQ]; rfl
        have hpc' : thc.st.st.2 = L.lab ".Lwc_main.x3" + 94 := by
          rw [hpcC, Spike.Lib.X64HelloPreA.cloneAtH, hexe _ _ _ _ _ _ hP]
        have hown : ExtRows.OwnOk (ownGHXW L a thc.st) d.1.mem thc.prom := hDo thc.st th0c.stack ▸ hOwnOk
        exact Spike.Lib.X64.HelloPh.selfWords_clone hlab (Spike.Lib.X64.HelloPh.spPool_of_ownedH hO htop hr0sz) hpc'
          hown }
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

/-- info: 'Spike.Lib.X64HelloHPre.hpre_ofH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hpre_ofH

/-- info: 'Spike.Lib.X64HelloHPre.wakeOwnXW_inj_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wakeOwnXW_inj_at

/-- info: 'Spike.Lib.X64HelloHPre.wakeOwnXW_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wakeOwnXW_inj

/-- info: 'Spike.Lib.X64HelloHPre.ne_wakeOwnXW_of_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ne_wakeOwnXW_of_nil

end Spike.Lib.X64HelloHPre
