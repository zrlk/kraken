/-
**The refusal path's obligations at hello's root level** (x86-64; twin of `Spike/Lib/A64HelloRefRoot.lean`; wake's
`WakeRefStub.refObl` at its root): `RefH.RefOblH` at the root's third level `W2Ig own ∧ X2I` under
`TakeCKS (L.lab siteL) (ClH L)`, the ghosts `GJ1RH` and `h2`'s placement `lbl2H`, from `RefO.refOblH_of` and its
pieces: the blocks (`RefBlkH.refBlkH`), `SFactsAC` (`refACH`), `ownGH`'s agreement, the abort's phase, no write,
the abort band (`refAgH`, `refAbStH`, `refNoWrH`, `refAbWH`), the map into the level (`refMapH`).

`RefPreH`'s facts give `PreH`'s (`preH_of`): the region's by `BoxPureH`; the slice's words and main's id at the
caller's entry state (`FrMGH`) by `X64HelloH2G.hG_of` at `GJ1RH`'s `GJ1H`; the box at `b'` by `upd`.

- `preH_of`: `refOblH_of`'s `hpre` at `GJ1RH` and `lbl2H`.
- `refOblH_ofX`: `refOblH_of` with `CstOkH` at the blocks and along the threads abort path, at a level `Wn` that
  `Wb` with `CstOkH` gives.
- `refOblH_rootX`: `RefOblH` at the root's level at the self words (`W2Ig ownGHXW`), generic in the memory side `ms`
  (its kernel `hK`, the exit call an abort site `hex`, e.g. `refExH`), the level's debts covering `DtW` (`hDt`),
  given `CstOkH` at the blocks and along the path.

No absolute address appears in a statement here.

## Unlike AArch64

- The code is `helloCells` with labels by `codeLabel` (AArch64 `helloProg`, `codeOf`); the kernel is `X64.abi`.
- `BoxPureH`'s and `PreH`'s region facts are x86-64's (`R.lo ≤ -384`, `16 ≤ R.hi`, base `96` below stack 0's top;
  AArch64 `-400`, `0`, `80`); `preH_of` moves them unchanged.
- main also holds its own and the worker's TCB words on the refusal path (`ownGHXW`), so the root's level there is
  `W2Ig ownGHXW` (`refOblH_ofX`, `refOblH_rootX`; AArch64 `refOblH_root`, at `ownGH`).
-/
import Spike.Lib.X64HelloRefMap
import Spike.Lib.X64HelloRefBlk
import Spike.Lib.X64HelloRefAb
import Spike.Lib.X64HelloRefAC
import Spike.Lib.X64HelloRootInst
import Spike.Lib.X64HelloOwnCstX
import Spike.Lib.X64WakeOwnWfApp

namespace Spike.Lib.X64.HelloPh.RefO

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Region FragS Arena MemSide)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (TakeCKS updN)
open Spike.Lib.X64.Flow.Ret0.StackTake (siteL)
open Spike.Lib.X64.HelloPh (ClH lo lbl2H X2I)
open Spike.Lib.X64.HelloPh.RootHP (GJ1RH)
open Spike.Lib.X64.HelloPh.RefH (RefPreH RefOblH)
open Spike.Lib.X64HelloHMid (slWsH)
open Spike.Lib.X64WakeSrcDefs (mainTidLbl)
open Scc.Sem.X64 (codeLabel)

/-- **`refOblH_of`'s `hpre` at the root** (`GJ1RH` at `upd lbl l b` and rodata's `l`, the placement `lbl2H`):
`BoxPureH` gives the region's facts, `hG_of` at `FrMGH`'s entry state the slice's words and main's id (the box
`l'` fresh, `hl'`; main's id at its TCB, `hmt`), `upd` the box at `b'`. -/
theorem preH_of {L : RuntimeLayout} {F0 : MachineData → Prop} {lbl : Lbl} {l : WeakMem.AllocLabel} {b : Nat}
    {l' : WeakMem.AllocLabel} {b' n' : Nat} (hl' : Spike.Lib.X64ConsumerA.upd lbl l b l' = none)
    (hmt : Spike.Lib.X64ConsumerA.upd lbl l b (mainTidLbl 2) = some (L.pinA.toNat + 8)) :
    ∀ R cP sl cA me, RefPreH L F0 (GJ1RH L (Spike.Lib.X64ConsumerA.upd lbl l b) l) l' b' (slWsH l) n' R cP sl cA me →
      PreH L (lbl2H lbl l b l' b') l' (slWsH l) R cP sl cA me := by
  rintro R cP sl cA me ⟨⟨F, J1, t, fr, ⟨hR, hal, -, hlo, hhi, hbase, -⟩, hG, ⟨σe, c, hJ, -, rfl, rfl⟩, hsrc⟩, hcA⟩
  obtain ⟨hsl, hme⟩ := Spike.Lib.X64HelloH2G.hG_of (b' := b') hl' hmt R F J1 t hG.1 σe c hJ
  refine ⟨hsrc, hsl, ?_, hme, hR, hal, hlo, hhi, hbase⟩
  show (if l' = l' then some b' else _) = _
  simp only [↓reduceIte]; rw [hcA]

variable {L : RuntimeLayout} (hp : L.prog = SccCode.helloCells) (hlo : L.Λ.code.lo = lo)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo SccCode.helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab siteL).toBitVec.toNat)

section OfX

open Spike.Lib.X64 (BlkW NodeW DFrame CKept Abs)
open Spike.Lib.X64.WakeRefTP (TPathW)
open Spike.Lib.X64.ThreadsAb (raT)
open Spike.Lib.X64.WakeWf (NoWrC)

variable {F0 : MachineData → Prop}
  {G : Region → (MachineData → Prop) → (Spike.Lib.X64.AS → Ctl → Prop) → UInt64 → Prop}
  {l : WeakMem.AllocLabel} {b : Nat} {ws : List TermRun.Word} {n : Nat} {Wb Wn : FragS isa}
  {K : State → State → Prop} {lbl : Lbl} {ms : List TermRun.Frame → MemSide isa} {ar : Arena} {lsize : Lsize}
  {Ctx : FragS isa}

set_option hygiene false in
/-- `CstOkH` at the reserve's counter. -/
local notation "CST" => fun (s : State) (_ : Ctl) =>
  Spike.Lib.X64.HelloPh.CstOkH (Spike.Lib.X64.PhRec.μ L) L (Spike.Lib.X64.Rt.Reserve.ntA L.lab) s

/-- **`RefOblH` from its pieces at a level needing `CstOkH`** (`refOblH_of` with one more path piece): the test and
three blocks inside `Wb` (`hblk`) and with `CstOkH` (`hcblk`) are inside `Wn` (`hlift`); the threads abort path's
components with `CstOkH` along it (`hcst`) are mapped into `Wn` (`hmap`). -/
theorem refOblH_ofX (hp : L.prog = SccCode.helloCells) (hK : (ms []).K = some abi)
    (hpre : ∀ R cP sl cA me, RefPreH L F0 G l b ws n R cP sl cA me → PreH L lbl l ws R cP sl cA me)
    (hblk : BlkH L lbl l ws (fun s c => Wb s c []) K) (hcblk : BlkH L lbl l ws (CST) (fun _ _ => False))
    (hlift : ∀ s c, Wb s c [] → (CST) s c → Wn s c [])
    (hac : ACH L lbl l ws ar lsize) (hag : AgH L lbl l ws) (habs : AbStH L lbl l ws)
    (hnw : NoWrH L lbl l ws ar lsize Ctx) (habw : AbWH L lbl l ws)
    (hcst : TOblH L lbl l ws (fun _ => CST) (fun _ _ => False))
    (hmap : ∀ (R' : Region) (s : State) (c : Ctl), ACWH L lbl ar lsize s c →
      Spike.Lib.X64.HelloPh.AgWH L (Spike.Lib.X64.Rt.Reserve.ntA L.lab) (ownWH L) (Spike.Lib.X64.PhRec.μ L) s c →
      Spike.Lib.X64ConsumerA.AbSt (Spike.Lib.X64.PhRec.μ L) (Spike.Lib.X64.WriteAb.Ab L.lab) s →
      NoWrC ar Spike.Lib.X64HelloSrc.helloSrc lbl lsize Ctx [] s c →
      Spike.Lib.X64.WakePh.AbW L R' (raT L.lab ".Lwc_main") (Spike.Lib.X64.PhRec.μ L) s c → (CST) s c →
      Wn s c [] ∧ ∀ s', ¬ K s s')
    (hex : ExH L (ms [])) :
    RefOblH L F0 G l b ws n Wn K lbl ms := by
  haveI := L.valid
  intro R m0 cP sl cA me hR0
  have hpre' := hpre R cP sl cA me hR0
  obtain ⟨-, -, -, -, hR, -, hlo, hhi, -⟩ := id hpre'
  obtain ⟨hts, hje, hx26, hfl⟩ := hblk R m0 cP sl cA me hpre'
  obtain ⟨cts, cje, cx26, cfl⟩ := hcblk R m0 cP sl cA me hpre'
  have hb : ∀ {nd : Spike.Lib.X64.ND} {blk : List (Directive × Nat)},
      BlkW (fun s c => Wb s c []) K L.exe L.endPc R (DFrame R m0) nd blk →
      BlkW (CST) (fun _ _ => False) L.exe L.endPc R (DFrame R m0) nd blk →
      BlkW (fun s c => Wn s c []) K L.exe L.endPc R (DFrame R m0) nd blk :=
    fun h₁ h₂ s σ c he hn hd hp hA hF hJ k hk m hA' hD =>
      ⟨hlift _ c (h₁ s σ c he hn hd hp hA hF hJ k hk m hA' hD).1 (h₂ s σ c he hn hd hp hA hF hJ k hk m hA' hD).1,
        (h₁ s σ c he hn hd hp hA hF hJ k hk m hA' hD).2⟩
  refine ⟨fun s c hA => ⟨hlift s c (hts s c hA).1 (cts s c hA).1, (hts s c hA).2⟩, hb hje cje, hb hx26 cx26,
    hb hfl cfl, fun m1 σC c0 hE => ?_⟩
  have h1 := TPathW.and (hac R m0 cP sl cA me m1 σC c0 hpre' hE) (hag R m0 cP sl cA me m1 σC c0 hpre' hE)
    fun s c h₁ h₂ => And.intro h₁ h₂
  have h2 := TPathW.and h1 (habs R m0 cP sl cA me m1 σC c0 hpre' hE) fun s c h₁ h₂ => And.intro h₁ h₂
  have h3 := TPathW.and h2 (hnw R m0 cP sl cA me m1 σC c0 hpre' hE) fun s c h₁ h₂ => And.intro h₁ h₂
  have h4 := TPathW.and h3 (habw R m0 cP sl cA me m1 σC c0 hpre' hE) fun s c h₁ h₂ => And.intro h₁ h₂
  have h4' := TPathW.and h4 (hcst R m0 cP sl cA me m1 σC c0 hpre' hE) fun s c h₁ h₂ => And.intro h₁ h₂
  have h5 := mapWKH (W' := fun s c => Wn s c []) (K' := K) h4'
    fun s c h _ => hmap _ s c h.1.1.1.1.1 h.1.1.1.1.2 h.1.1.1.2 h.1.1.2 h.1.2 h.2
  have hlays : Scc.Cert.Rt.X64.Lays L.exe SccCode.helloCells L.pfx := hp ▸ L.lays
  have hend : L.endPc = Scc.Cert.Rt.X64.endOf L.exe SccCode.helloCells L.pfx := by
    show Scc.Cert.Rt.X64.endOf L.exe L.prog L.pfx = _; rw [hp]
  exact TPathW.stub h5 hlays hend SccCode.hello_abort hK
    (Spike.Lib.X64.fstable_enter hR (Spike.Lib.X64.FStable.dframe R m0) (by omega) (by decide) (by omega)
      (by omega) (by decide) (by decide) (by decide))
    fun s _ ⟨_, _, _, hpc, _⟩ => hex s hpc

include hp hlo hΛ hlab in
/-- **`RefOblH` at the root's level at the self words** (`h2Stmt_rootX`'s `hobl` at `W2Ig ownGHXW ∧ X2I`, `GJ1RH`,
`lbl2H`): `refOblH_ofX` at the pieces (`preH_of`, `RefBlkH.refBlkH`, `refACH`, `refAgH`, `refAbStH`, `refNoWrH`,
`refAbWH`, `refMapH`), given `CstOkH` at the four blocks (`hcblk`) and along the threads abort path (`hcst`); `W2H`
with `CstOkH` is the level at `ownGHXW` (`Wf.appendS` twice). -/
theorem refOblH_rootX {Dt : State → Prop} {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel}
    {b' n' : Nat}
    (hl' : Spike.Lib.X64ConsumerA.upd lbl l b l' = none)
    (hmt : Spike.Lib.X64ConsumerA.upd lbl l b (mainTidLbl 2) = some (L.pinA.toNat + 8))
    (hDt : ∀ s, Spike.Lib.X64.WakeWf.DtW s → Dt s) (hK : (ms []).K = some abi) (hex : ExH L (ms []))
    (hcblk : ∀ ws, BlkH L (lbl2H lbl l b l' b') l' ws (CST) (fun _ _ => False))
    (hcst : ∀ ws, TOblH L (lbl2H lbl l b l' b') l' ws (fun _ => CST) (fun _ _ => False)) :
    RefOblH L F0 (GJ1RH L (Spike.Lib.X64ConsumerA.upd lbl l b) l) l' b' (slWsH l) n'
      (fun s c fs => W2Ig (ownGHXW L (Spike.Lib.X64.Rt.Reserve.ntA L.lab)) L ar Dt Ctx lbl lsize l b n l' b' n' s c fs ∧
        X2I L lbl lsize l b n l' b' n' s c fs)
      (TakeCKS (L.lab siteL) (ClH L)) (lbl2H lbl l b l' b') ms := by
  have hlift : ∀ s c, (Spike.Lib.X64.HelloPh.RootWX.W2H L (Spike.Lib.X64.Rt.Reserve.ntA L.lab) ar
      Spike.Lib.X64HelloSrc.helloSrc Dt (ClH L) (fun _ _ _ => False) (lbl2H lbl l b l' b')
        (updN (updN lsize l n) l' n') s c [] ∧ X2I L lbl lsize l b n l' b' n' s c []) → (CST) s c →
      W2Ig (ownGHXW L (Spike.Lib.X64.Rt.Reserve.ntA L.lab)) L ar Dt Ctx lbl lsize l b n l' b' n' s c [] ∧
        X2I L lbl lsize l b n l' b' n' s c [] :=
    fun _ _ h hc => ⟨⟨h.1.1, (h.1.2.appendS hc.1).appendS hc.2⟩, h.2⟩
  exact refOblH_ofX (F0 := F0) (n := n') (ar := ar) (lsize := updN (updN lsize l n) l' n')
    (Ctx := fun _ _ _ => False)
    (Wb := fun s c fs => Spike.Lib.X64.HelloPh.RootWX.W2H L (Spike.Lib.X64.Rt.Reserve.ntA L.lab) ar
      Spike.Lib.X64HelloSrc.helloSrc Dt (ClH L) (fun _ _ _ => False) (lbl2H lbl l b l' b')
        (updN (updN lsize l n) l' n') s c fs ∧ X2I L lbl lsize l b n l' b' n' s c fs) hp hK (preH_of hl' hmt)
    (Spike.Lib.X64.HelloPh.RefBlkH.refBlkH hp hlo hΛ hlab)
    (hcblk _) hlift (refACH hp hlo hlab hΛ _ _ _ ar _) (refAgH hp hlo hlab _ _ _) (refAbStH hp hlo hlab _ _ _ hΛ)
    (refNoWrH hp hlo hlab _ _ _ ar _ _) (refAbWH hp hlo hlab _ _ _) (hcst _)
    (fun R' s c hac hag habs hnw habw hc =>
      have h := refMapH hlab hDt (lbl2H lbl l b l' b') ar (updN (updN lsize l n) l' n') (fun _ _ _ => False) L.endPc
        (lbl2H lbl l b l' b') (updN (updN lsize l n) l' n') R' s c hac hag habs hnw habw
      ⟨hlift s c h.1 hc, h.2⟩) hex

end OfX

end Spike.Lib.X64.HelloPh.RefO

/-- info: 'Spike.Lib.X64.HelloPh.RefO.preH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.preH_of

/-- info: 'Spike.Lib.X64.HelloPh.RefO.refOblH_ofX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.refOblH_ofX

/-- info: 'Spike.Lib.X64.HelloPh.RefO.refOblH_rootX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RefO.refOblH_rootX
