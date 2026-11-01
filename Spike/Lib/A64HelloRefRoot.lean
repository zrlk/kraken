/-
**The refusal path's obligations at hello's root level** (AArch64; piece R7;
wake's `WakeRefStub.refObl` at its root): `RefH.RefOblH` at the root's third level `W2I ∧ X2I` under
`TakeCKS (L.lab siteL) (ClH L)`, the ghosts `GJ1RH` and `h2`'s placement `lbl2H`, from `RefO.refOblH_of` and its
pieces: the blocks (`RefBlkH.refBlkH`, R6), `SFactsAC` (`refACH`, R4), `ownGH`'s agreement, the abort's phase, no
write, the abort band (`refAgH`, `refAbStH`, `refNoWrH`, `refAbWH`, R3), the map into the level (`refMapH`, R5).

`RefPreH`'s facts give `PreH`'s (`preH_of`): the region's by `BoxPureH`; the slice's words and main's id at the
caller's entry state (`FrMGH`) by `HelloH2G.hG_of` at `GJ1RH`'s `GJ1H`; the box at `b'` by `upd`.

- `preH_of`: `refOblH_of`'s `hpre` at `GJ1RH` and `lbl2H`.
- `refOblH_root`: `RefOblH` at the root's level, generic in the memory side `ms` (its kernel `hK`, the exit call
  an abort site `hex`, e.g. `refExH`) and given the level's debts cover `DtW` (`hDt`, row B8-h2-refObl-hDt).

No absolute address appears in a statement here.
-/
import Spike.Lib.A64HelloRefMap
import Spike.Lib.A64HelloRefBlk
import Spike.Lib.A64HelloRootInst

namespace Spike.Lib.A64.HelloPh.RefO

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib (Region FragS Arena MemSide)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (TakeCKS updN)
open Spike.Lib.A64.Flow.Ret0.StackTake (siteL)
open Spike.Lib.A64.HelloPh (ClH lo lbl2H W2I X2I)
open Spike.Lib.A64.HelloPh.RootHP (GJ1RH)
open Spike.Lib.A64.HelloPh.RefH (RefPreH RefOblH)
open Spike.Lib.HelloHMid (slWsH)
open Spike.Lib.WakeT1 (mainTidLbl)
open Scc.Cert.Link.A64 (codeOf)

/-- **`refOblH_of`'s `hpre` at the root** (`GJ1RH` at `upd lbl l b` and rodata's `l`, the placement `lbl2H`):
`BoxPureH` gives the region's facts, `hG_of` at `FrMGH`'s entry state the slice's words and main's id (the box
`l'` fresh, `hl'`; main's id at its TCB, `hmt`), `upd` the box at `b'`. -/
theorem preH_of {L : RuntimeLayout} {F0 : MachineData → Prop} {lbl : Lbl} {l : WeakMem.AllocLabel} {b : Nat}
    {l' : WeakMem.AllocLabel} {b' n' : Nat} (hl' : Spike.Lib.A64ConsumerA.upd lbl l b l' = none)
    (hmt : Spike.Lib.A64ConsumerA.upd lbl l b (mainTidLbl 2) = some (L.pinA.toNat + 8)) :
    ∀ R cP sl cA me, RefPreH L F0 (GJ1RH L (Spike.Lib.A64ConsumerA.upd lbl l b) l) l' b' (slWsH l) n' R cP sl cA me →
      PreH L (lbl2H lbl l b l' b') l' (slWsH l) R cP sl cA me := by
  rintro R cP sl cA me ⟨⟨F, J1, t, fr, ⟨hR, hal, -, hlo, hhi, hbase, -⟩, hG, ⟨σe, c, hJ, -, rfl, rfl⟩, hsrc⟩, hcA⟩
  obtain ⟨hsl, hme⟩ := Spike.Lib.HelloH2G.hG_of (b' := b') hl' hmt R F J1 t hG.1 σe c hJ
  refine ⟨hsrc, hsl, ?_, hme, hR, hal, hlo, hhi, hbase⟩
  show (if l' = l' then some b' else _) = _
  simp only [↓reduceIte]; rw [hcA]

variable {L : RuntimeLayout} (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
  (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take = some (L.lab siteL).toBitVec.toNat)

include hp hlo hΛ hlab hsite in
/-- **`RefOblH` at the root's level** (`h2Stmt_root`'s `hobl` at `W2I ∧ X2I`, `GJ1RH`, `lbl2H`, given the memory
side's kernel `hK` and its exit abort site `hex`): `refOblH_of` at the pieces R3–R6, the level's debts covering
`DtW` (`hDt`). `W2I` is `RootWX.W2H` at the empty context and the sizes `updN (updN lsize l n) l' n'`
(`HelloW2.w2H_def`, by unfolding), so the pieces are taken there. -/
theorem refOblH_root {F0 : MachineData → Prop} {ar : Arena} {Dt : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl}
    {lsize : Lsize} {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat}
    {ms : List TermRun.Frame → MemSide isaLSE2} (hl' : Spike.Lib.A64ConsumerA.upd lbl l b l' = none)
    (hmt : Spike.Lib.A64ConsumerA.upd lbl l b (mainTidLbl 2) = some (L.pinA.toNat + 8))
    (hDt : ∀ s, Spike.Lib.A64.WakeWf.DtW s → Dt s) (hK : (ms []).K = some abi) (hex : ExH L (ms [])) :
    RefOblH L F0 (GJ1RH L (Spike.Lib.A64ConsumerA.upd lbl l b) l) l' b' (slWsH l) n'
      (fun s c fs => W2I L ar Dt Ctx lbl lsize l b n l' b' n' s c fs ∧ X2I L lbl lsize l b n l' b' n' s c fs)
      (TakeCKS (L.lab siteL) (ClH L)) (lbl2H lbl l b l' b') ms := by
  exact refOblH_of (F0 := F0) (n := n') (ar := ar) (lsize := updN (updN lsize l n) l' n')
    (Ctx := fun _ _ _ => False)
    (Ws := fun s c fs => Spike.Lib.A64.HelloPh.RootWX.W2H L (Spike.Lib.A64.Rt.Reserve.ntA L.lab) ar
      Spike.Lib.HelloSrc.helloSrc Dt (ClH L) (fun _ _ _ => False) (lbl2H lbl l b l' b')
        (updN (updN lsize l n) l' n') s c fs ∧
      X2I L lbl lsize l b n l' b' n' s c fs) hp hK
    (preH_of hl' hmt) (Spike.Lib.A64.HelloPh.RefBlkH.refBlkH hp hlo hΛ hlab hsite)
    (refACH hp hlo hlab hΛ _ _ _ ar _) (refAgH hp hlo hlab _ _ _) (refAbStH hp hlo hlab _ _ _ hΛ)
    (refNoWrH hp hlo hlab _ _ _ ar _ _) (refAbWH hp hlo hlab _ _ _)
    (refMapH hlab hDt (lbl2H lbl l b l' b') ar (updN (updN lsize l n) l' n') (fun _ _ _ => False) L.endPc
      (lbl2H lbl l b l' b') (updN (updN lsize l n) l' n')) hex

end Spike.Lib.A64.HelloPh.RefO

/-- info: 'Spike.Lib.A64.HelloPh.RefO.preH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefO.preH_of

/-- info: 'Spike.Lib.A64.HelloPh.RefO.refOblH_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RefO.refOblH_root
