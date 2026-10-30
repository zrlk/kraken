/-
**wake.w on AArch64: `WakeSpawnR.HPre` from the pre-spawn relation**: `hpre_of`, the pre-spawn segment's end at
main's clone, for any relation `R1` below `WakeO.R1O … D` at the placed
layout `Ly := RuntimeLayout.ofPlaceW hp i` (the instance's `R1 = R1O ∧ VPriv`).

From `R1O`'s conjuncts at the `SpawnPrem` (its `PostSAH` branch is out:
the process has not exited):

- `RSAH`'s `PreJAH` gives main's thread `th` (so `tid = 0`), its source
  thread `th0`, the placement `lbl`/`lsize`, `Inv1` and the side facts
  `SpawnPre` copies (`msgs`, `memIn`, `fits`, `bnd`, `own`, `slots`);
- `NoObs` gives `main` not returned (the run) and the empty trace;
- `VPre` gives the run (`run_spawnCfg`) and `LtPre` (`vpre_spawn`);
- `VPreC` gives `p`'s words `[c, me]` (`PB`) and the spawn's coherence
  (`scov_of`);
- `VFlag` gives the flag's last source write `0` (`vflag_spawn`), at the
  target by `Inv1` (`SpawnFlag.flag_at`).

The spawned configuration is `spawnCfg s 0 th0 "t" mTail "worker" [] Ty
[c, me]`, the record `recW d.1.mem.last s.mem.size lbl lsize l pT w1` with
`w1`, `w2` the bumped words and `GhOK` by `WakeWorkerR.ghOK_of_clone`.

**Premises**:

- `hR1`: `R1` below `R1O arch Ly.Λ μ' D` (the instance's `R1` is `R1O ∧ VPriv`);
- `hr0`, `hr1` (`rfl` at constant ranges `D.r0`, `D.r1 = r1Of Ly.lab`):
  the record's ranges are the data's;
- `hG`: `D.G` is below the clone's record's guarantee `wakeG'` (its
  flag word `cT` at `c`'s label `l` under `I2`'s placement);
- `hCl` (from `WakeWc.i2_cloneInv`): at the clone, for `PreJAH`'s
  witnesses, `ClonePre` at `D.r0` and `r1Of Ly.lab` with its `X` and a
  `Q2` request `q`, main's source stack empty, `c`'s label holding a word,
  and main's id register (`PreR.hme`).
-/
import Spike.Lib.WakeSpawnR
import Spike.Lib.WakeO

namespace Spike.Lib.WakeHPre

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeW1 Spike.Lib.WakeT1
open Spike.Lib.A64.Rt (RuntimeLayout TcbGG tcbOf)
open Spike.Lib.A64.Rt.PreChild (r1Of)
open Spike.Lib.WakeInst (Gh wakeG')
open Spike.Lib.WakeOkW (recW)
open Spike.Lib.WakeSpawn (SpawnPrem SpawnPre)
open Spike.Lib.WakeTcbArea (Q2)
open Spike.Lib.WakePreA (ClonePre cloneAt)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib.A64Consumer (HeldOk2 Lbl Lsize)
open Spike.Lib.A64ConsumerA (I2)
open Spike.Lib.WakeSpawnR (ιR endR QG HPre PreR)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- **`HPre` from `R1O`** (see the module doc). -/
theorem hpre_of {asm : String} {E : Entry} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks}
    {M : WakeM0.MSide (ιR hp i)} {r0 r1 : ιR hp i → Range} {D : WakeO.OData} {μ' : Marks}
    (hR1 : ∀ d s, R1 d s → WakeO.R1O arch (Ly).Λ μ' D d s)
    /- the record's ranges are the data's -/
    (hr0 : ∀ w, r0 w = D.r0) (hr1 : ∀ w, r1 w = r1Of (Ly).lab)
    /- the data's guarantee is below the clone's record's (at `c`'s label `l`
    under `I2`'s placement `lbl`) -/
    (hG : ∀ d s (th : Thread isaLSE2) (th0 : TermRun.TTh) (lbl : Lbl) (lsize : Lsize) ts hd l T S pT cw,
      R1 d s → d.1.threads = #[th] → s.ths = #[th0] →
      I2 D.ar D.L0 D.ls0 D.inv0 D.inv1 lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) →
      Inv1 (Ly).Λ lbl lsize ts th d.1.mem s.mem → ∀ X, ClonePre pfxM (Ly).Λ D.r0 (r1Of (Ly).lab) X lbl d s →
      MemInv D.G d.1.mem → MemInv (wakeG' hp i (recW T S lbl lsize l pT cw)) d.1.mem)
    /- the clone's facts at `PreJAH`'s witnesses -/
    (hCl : ∀ d s th stack tls r (th0 : TermRun.TTh) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
      (hd : Option (Nat × TermRun.Word)),
      SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
      d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
      I2 D.ar D.L0 D.ls0 D.inv0 D.inv1 lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      HeldOk2 (Ly).Λ D.r0 D.r1 th.st d.2.held → Inv1 (Ly).Λ lbl lsize ts th d.1.mem s.mem →
      ∃ (X : State → Prop) (q : TcbGG), ClonePre pfxM (Ly).Λ D.r0 (r1Of (Ly).lab) X lbl d s ∧
        (∀ st, X st → st.exe = (Ly).exe ∧ st.endPc = endR hp i ∧ st.decls = {}) ∧
        (∀ st, X st → st.st.2 = cloneAt pfxM (Ly).exe ∧
          (st.st.1.regs.getXReg .X3).toBitVec = tcbOf (Ly).lab q) ∧
        Q2 q ∧ th0.stack = [] ∧
        (∀ l, TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) →
          0 < lsize l) ∧
        BitVec.ofNat 64 (th.st.st.1.regs.getXReg .X10).toNat + 16#64 = (Ly).pinA + 24#64) :
    HPre hp i asm E arch R1 μ M r0 r1 := by
  intro tid d s th stack tls r hP
  obtain ⟨h1, -, h3, -, -, h6, h7, -⟩ := id hP
  obtain ⟨⟨⟨⟨hRS, hNo⟩, hV⟩, hC⟩, hF⟩ := hR1 _ _ h1
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
  obtain ⟨X, q, hcl, hX, hXq, hq, hstk, hin, hme⟩ :=
    hCl d s th stack tls r th0 lbl lsize ts hd hP hth hs hσ hp0 hJ (hheld0 ▸ hH) hInv1
  have hcl0 := hcl
  obtain ⟨thc, th0c, tlsc, cA, meW, l, hthc, hsc, -, -, hprom, hcall, -, -, -, -, hheld, -, -, -, -, -, -, -, -,
    hterm, hc, hme', htidl, hvc, -⟩ := hcl0
  obtain rfl : thc = th := by
    rw [hth] at hthc; exact (List.singleton_inj.mp (congrArg Array.toList hthc)).symm
  obtain rfl : th0c = th0 := by
    rw [hs] at hsc; exact (List.singleton_inj.mp (congrArg Array.toList hsc)).symm
  have hin0 := hin l hc
  have h0 : s.ths[0]? = some th0c := by rw [hs]; rfl
  have hsz : s.ths.size = 1 := by rw [hs]; rfl
  -- `p`'s words are `c`'s and `me`'s
  obtain ⟨th0', h0', -, hPB⟩ := hC hsz
  obtain rfl : th0c = th0' := by rw [h0] at h0'; exact Option.some.inj h0'
  obtain ⟨tc, wc, tm, wm, hlc, hlm, hlp⟩ := hPB hterm
  rw [show TermRun.lookupE th0c.env "c" = _ from hc] at hlc
  rw [show TermRun.lookupE th0c.env "me" = _ from hme'] at hlm
  simp only [Option.some.injEq, Prod.mk.injEq] at hlc hlm
  obtain ⟨rfl, rfl⟩ := hlc
  obtain ⟨rfl, rfl⟩ := hlm
  -- the run and `LtPre`
  have hex := (WakeNoObs.NoObs.traceOf_nil hNo h6).2
  have hrun := SpawnViewLtSteps.run_spawnCfg (arch := arch) h0 hterm hp0 (by rw [hsz]; decide) hlp hex
  obtain ⟨hvl, henv⟩ := SpawnViewLtSteps.vpre_spawn hV hsz h0 hterm
  have hths : (TermSpawnStep.spawnCfg s 0 th0c "t" WakeM0.mTail "worker" [] (.prod (.ptr .pub .int) .tid)
      ([TermRun.cst (.loc ⟨l, 0⟩ 0)] ++ [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])).ths =
      #[TermSpawnStep.spawnPar s 0 th0c "t" WakeM0.mTail,
        TermSpawnStep.spawnKid s 0 th0c "worker" [] (.prod (.ptr .pub .int) .tid)
          ([TermRun.cst (.loc ⟨l, 0⟩ 0)] ++ [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])] := by
    simp [TermSpawnStep.spawnCfg, TermSpawnStep.spawnT, hs]
  have hsc := SpawnCohSteps.scov_of hC hs hp0 rfl hths
  -- the flag
  obtain ⟨i', j', hij, hi, hj, hv⟩ := SpawnFlag.vflag_spawn hF hs hterm hp0 hc
  have hvc0 := hvc
  obtain ⟨-, x, hx, -⟩ := hvc0
  obtain ⟨A, hA⟩ : ∃ A, lbl l = some A := by
    cases h : lbl l with
    | none => simp [wordAddr, h] at hx
    | some A => exact ⟨A, rfl⟩
  have hwf := WakeQ.hwf_ofPlaceOK hp i
  obtain ⟨k', hread, hlast⟩ := SpawnFlag.flag_at hInv1 hprom hwf hA hij hi hj hv
  have hS : 0 < s.mem.size := by
    obtain ⟨m, hm, -⟩ := hi; exact Nat.lt_of_le_of_lt (Nat.zero_le _) (TermLiveProps.lt_of_get hm)
  have hgh := WakeWorkerR.ghOK_of_clone (T := d.1.mem.last) (pT := wordLoc 0)
    (cw := TermSpawn.bumpW (TermSpawnStep.spawnS s th0c).vs.vRelSt (TermRun.cst (.loc ⟨l, 0⟩ 0)))
    hInv1.mem hwf hvc rfl hin0 hS
  have hsrc := SpawnViewLtSteps.src_fields (s := s) (i := 0) hc hA hin0
  refine ⟨rfl, _, (⟨_, hgh⟩ : ιR hp i), TermSpawnStep.spawnPar s 0 th0c "t" WakeM0.mTail,
    TermSpawnStep.spawnKid s 0 th0c "worker" [] (.prod (.ptr .pub .int) .tid)
      ([TermRun.cst (.loc ⟨l, 0⟩ 0)] ++ [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)]),
    lbl, lsize, ts, k', D.own thc.st th0c.stack, d.1.mem.last, s.mem.size, l,
    wordLoc 0, TermSpawn.bumpW (TermSpawnStep.spawnS s th0c).vs.vRelSt (TermRun.cst (.loc ⟨l, 0⟩ 0)),
    TermSpawn.bumpW (TermSpawnStep.spawnS s th0c).vs.vRelSt (TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)), .prod (.ptr .pub .int) .tid, D.r0, X, q, hrun, ?_⟩
  exact {
    clone := hcl
    hX := hX
    hXq := hXq
    hq := hq
    hc := ⟨th0c, hs, hc⟩
    hw := rfl
    pre := {
      SR := rfl
      threads := hth
      ths := hths
      inv1 := hInv1
      prom := hprom
      msgs := hOwnM
      memIn := hMemIn
      fits := hFits
      memInv := hG d s thc th0c lbl lsize ts hd l _ _ _ _ h1 hth hs hJ hc hInv1 X hcl hMemInv
      bnd := hBnd
      own := hOwnOk
      sp0 := hp0
      sp1 := rfl
      scov0 := fun k m hm _ => hsc.1 k m hm
      scov1 := fun k m hm _ => hsc.2 k m hm
      flag := hread
      flagLast := hlast
      st1 := rfl
      σ1 := rfl
      term1 := rfl
      env1 := ⟨.ptr .pub .int, .tid, [.one], _, rfl, rfl, rfl, ⟨.pub, .int, rfl, rfl⟩, rfl⟩
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
      trace := WakeNoObs.NoObs.run_nil hNo hrun h6 }
    hin := hin0
    hS := hS
    env1 := rfl
    hw1 := rfl
    hw2 := rfl
    stack0 := hstk
    σ0 := hσ
    term0 := .inl rfl
    env0 := ⟨_, _, _, hsrc.2.1, rfl, rfl⟩
    prom0 := hp0
    tid0 := by show th0c.tidLbl.orElse _ = _; rw [htidl]; rfl
    hme := hme
    hlt := ⟨th0c, _, _, _, _, _, hs, rfl, hvl ⟨l, 0⟩,
      fun w hw => henv _ (TermNoFul.lookupE_mem (env := th0c.env) (x := "p") hlp) w hw⟩
    hsp := ⟨th0c, _, hs, rfl⟩ }

/-- info: 'Spike.Lib.WakeHPre.hpre_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hpre_of

end Inst

end Spike.Lib.WakeHPre
