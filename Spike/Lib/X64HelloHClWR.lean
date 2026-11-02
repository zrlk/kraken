/-
**hello's clone facts from the pre-spawn relation** (x86-64; the twin of `Spike/Lib/A64HelloHClWR.lean`, at
hello's relation `X64HelloO.R1OH … X64HelloOLift.XH`): `X64HelloHPre.hpre_ofH`'s `hCl`, from
`X64HelloHClW.hClH_of`.

`hClH_of` takes main's state and call (`hth`, `hs`, `hsys`, `hcall`), the certificate (`hcert`), the held list
(`hH`), main's source id (`htid`) and the buffer fact (`hbuf`). At the relation these are:
- `hth`, `hs`, `hH` and the fragment state `hI`: `hpre_ofH`'s `hCl` quantifies them;
- `hsys`, `hcall`: `X64WakeSpawn.SpawnPrem`'s call;
- `hcert`: the relation's base `RSAH` is before the exit (`SpawnPrem`'s `exited = none`), whose `PreJAH` carries
  the certificate and the source reach;
- `htid`: thread 0 of every configuration hello's source reaches holds main's box label
  (`X64HelloMainTidLbl.mainTidLbl_of_reachH`);
- `hbuf`: the slot `XH`'s `VBufR` at the one pre-spawn thread with no promises (`X64HelloHbufR1.hbuf_XH`).

- `hClH_ofR`: `hpre_ofH`'s `hCl` at `Dd.r0 = r0Of`, `r1c = r1Of`, for any `inv2` with `hown2`/`hx1`.
- `hClH_ofRI`: the same at `Dd.inv2 = X64HelloH2Inv.inv2H …` (`hown2`/`hx1` by `own2_of`/`x1_2_of`), no
  clone-state premise left.

## Differences from the AArch64 version

- The child's stack top is in `%rsi` (`hx1`'s `get64 .rsi`; AArch64: `X1`).
- `ClonePreH` carries no label prefix (AArch64's `pfxM`); the certificate is at `Arch.tso`.
-/
import Spike.Lib.X64HelloHClWF
import Spike.Lib.X64HelloH2Inv
import Spike.Lib.X64HelloHPre
import Spike.Lib.X64HelloMainTidLbl
import Spike.Lib.X64HelloHbufR1

namespace Spike.Lib.X64HelloHClW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Entry Range Inv1)
open Scc.Sem.X64 (abi pcOf Asm)
open Spike.Lib (Arena FragS MemSide)
open Spike.Lib.X64WakeA64 (Cfg)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64HelloPreA (clonePcH ClonePreH H0StmtH H1StmtHF H2StmtH)
open Spike.Lib.X64HelloSrc (helloSrc helloS)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloQ (helloQ)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64HelloO (ODataH IH R1OH)
open Spike.Lib.X64HelloOLift (XH)
open Spike.Lib.X64HelloH2Inv (inv2H own2_of x1_2_of)
open Spike.Lib.X64WakeSrcDefs (mainTidLbl)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64.Rt.Ti2 (r0Of)

section Rel

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → Spike.Lib.Inv2Core.SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Spike.Lib.Inv2Core.Inv2Params isa}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : Spike.Lib.X64WakeM0.MSide ι} {D : WSideH ι}
  {r0 r1 : ι → Range} {asm : Asm} {E : Entry}
  {μ : Marks} {Dd : ODataH} {L : RuntimeLayout} {ab : Option (State → Prop)} {Cl : State → Prop}
  {W0 : FragS isa} {K : State → State → Prop} {ms0 : List TermRun.Frame → MemSide isa} {endPc : Int64}
  {Start : FragS isa} {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
  {Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop} {fr : List TermRun.Frame}
  {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
  {Box : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop}

/-- **`hpre_ofH`'s `hCl` from the pre-spawn relation** (module doc), at the data's ranges `r0Of`, `r1Of`
(`hr0`, `hr1`), for any `inv2` whose clone states own the child's stack with `%rsi` at its top (`hown2`,
`hx1`). The levels' statements (`h0`, `h1`, `h2`), the fragment's nodes and take site (`hN`, `hT`), the clone's
pc (`hCl`) and the stacks not wrapping (`hbd`) are `hClH_of`'s. -/
theorem hClH_ofR (hR1 : ∀ d s, R1 d s → R1OH arch L.Λ μ Dd XH d s)
    (hN : NodesA L.Λ helloSrc μ Dd.rd Dd.G Dd.own Dd.ar (IH Dd) ab Cl) (hT : TakeSiteS helloSrc μ (IH Dd))
    (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (h0 : H0StmtH W0 K Dd.L0 ms0 L Start Dd.inv0) (h1 : H1StmtHF W1 K Dd.ar Dd.L0 ms1 L Rd Dd.inv1 fr)
    (h2 : H2StmtH W2 K Dd.ar Dd.L0 ms2 L endPc Box Dd.inv2)
    (hr0 : Dd.r0 = r0Of L.lab) (hr1 : Dd.r1 = r1Of L.lab) (hbd : L.stacksA.toNat + 32768 < 2 ^ 64)
    (hown2 : ∀ l b n l' b' n' s c fs, Dd.inv2 l b n l' b' n' s c fs → pcOf s = clonePcH L →
      Owned L.Λ (r1Of L.lab) s)
    (hx1 : ∀ l b n l' b' n' s c fs, Dd.inv2 l b n l' b' n' s c fs → pcOf s = clonePcH L →
      s.st.1.regs.get64 .rsi = Spike.Lib.X64.Flow.WakeWc.kOf L.lab) :
    ∀ d s th stack tls r (th0 : TermRun.TTh) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
      (hd : Option (Nat × TermRun.Word)),
      SpawnPrem (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) L.Λ asm E 0 d s th stack tls r →
      d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
      IH Dd lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      HeldOk2 L.Λ Dd.r0 Dd.r1 th.st d.2.held → Inv1 L.Λ lbl lsize ts th d.1.mem s.mem →
      ∃ X : State → Prop, ClonePreH L.Λ Dd.r0 (r1Of L.lab) X lbl d s := by
  intro d s th stack tls r th0 lbl lsize ts hd hP hth hs _ hp hI hH _
  obtain ⟨h1R, -, -, h4, -, h6, h7, -⟩ := id hP
  obtain ⟨hRS, hX⟩ := hR1 _ _ h1R
  rcases hRS with hPre | ⟨_, _, _, _, _, _, _, _, _, _, ⟨_, hk⟩, _⟩
  case inr => rw [hk] at h6; cases h6
  obtain ⟨thm, th0', _, _, _, _, _, _, _, hthm, -, -, -, -, hcert, hs', -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨_, hreach⟩⟩ := hPre
  have htid : th0.tidLbl = some (mainTidLbl 2) := Spike.Lib.X64HelloMainTidLbl.mainTidLbl_of_reachH hreach hs
  obtain rfl : th = thm := by
    rw [hth] at hthm; exact List.singleton_inj.mp (congrArg Array.toList hthm)
  rw [hr0]
  refine ⟨(· = th.st), hClH_of hN hT hCl h0 h1.toH h2 hbd hown2 hx1 hth hs hI h4 h7 hcert (hr0 ▸ hr1 ▸ hH) htid ?_⟩
  exact Spike.Lib.X64HelloHbufR1.hbuf_XH hX hs hp

/-- **`hClH_ofR` at `inv2 := inv2H`** (`hinv2`): the clone states' facts are `X2H`'s (`own2_of`, `x1_2_of`). -/
theorem hClH_ofRI {a : Int64} {ls0 : Lsize} (hR1 : ∀ d s, R1 d s → R1OH arch L.Λ μ Dd XH d s)
    (hN : NodesA L.Λ helloSrc μ Dd.rd Dd.G Dd.own Dd.ar (IH Dd) ab Cl) (hT : TakeSiteS helloSrc μ (IH Dd))
    (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (h0 : H0StmtH W0 K Dd.L0 ms0 L Start Dd.inv0) (h1 : H1StmtHF W1 K Dd.ar Dd.L0 ms1 L Rd Dd.inv1 fr)
    (h2 : H2StmtH W2 K Dd.ar Dd.L0 ms2 L endPc Box Dd.inv2)
    (hr0 : Dd.r0 = r0Of L.lab) (hr1 : Dd.r1 = r1Of L.lab) (hbd : L.stacksA.toNat + 32768 < 2 ^ 64)
    (hinv2 : Dd.inv2 = inv2H W2 K ms2 L a endPc Dd.L0 ls0) :
    ∀ d s th stack tls r (th0 : TermRun.TTh) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
      (hd : Option (Nat × TermRun.Word)),
      SpawnPrem (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) L.Λ asm E 0 d s th stack tls r →
      d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
      IH Dd lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      HeldOk2 L.Λ Dd.r0 Dd.r1 th.st d.2.held → Inv1 L.Λ lbl lsize ts th d.1.mem s.mem →
      ∃ X : State → Prop, ClonePreH L.Λ Dd.r0 (r1Of L.lab) X lbl d s :=
  hClH_ofR hR1 hN hT hCl h0 h1 h2 hr0 hr1 hbd
    (fun _ _ _ _ _ _ _ _ _ hi hpc => by rw [hinv2] at hi; exact own2_of hi hpc)
    (fun _ _ _ _ _ _ _ _ _ hi hpc => by rw [hinv2] at hi; exact x1_2_of hi hpc)

end Rel

end Spike.Lib.X64HelloHClW

/-- info: 'Spike.Lib.X64HelloHClW.hClH_ofR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHClW.hClH_ofR

/-- info: 'Spike.Lib.X64HelloHClW.hClH_ofRI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHClW.hClH_ofRI
