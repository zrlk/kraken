/-
**main at the clone in `h2`'s invariant** (AArch64; layer 3, `hCP`; the
hello twin of the first three bullets of `Spike/Lib/A64WakeBoxW.lean`'s `hB_box`): `HelloH2Box.hB2_of`'s `hCP` at
`CP := HelloHMid.CloneMidH … l' b' n'` (the box's label `l'` at `b'`), `Cl := HelloPh.ClH L`.

At a `CloneMidH` state main is at the clone's `svc` (`wcNSH_clonePc`), a system call (`hello_svcIn`) that decodes
to a `clone` (`clone_decode_of_postH`), so it is `ClH`'s and off the take pc (`hna`); inside the level (`W` at no
frames); `X2H`'s clone clause holds: `x1` is `kOf` (`wcNSH`), `c`'s label is the box `l'` of `n' = 1` cell
(`SpawnSrcH`, `BoxPureH`), the child's stack owned from the level's extra fact at the clone (`Wc`, `StackM r1Of`
by the hat's late frame condition, `owned_of_stackM`), and `CloneInvH` (`hCI`); `X2H`'s take clause is vacuous.

- `cloneInvH_of_mid`: `hCI` from `CloneMidH` at a placement placing the box, given `G` pins the entry registers.
- `hCP_of`: `hCP` from `CloneMidH`, given `CloneInvH` there (`hCI`; its slice clause needs `CloneMidH` to keep the
  box's slice `ws` (threaded through `HelloHMid`) at `slWsH l`, and the entry registers of `Jr1`'s pin).
-/
import Spike.Lib.A64HelloH2Box
import Spike.Lib.A64HelloHatA
import Spike.Lib.A64HelloClH
import Spike.Lib.A64HelloChildAt
import Spike.Lib.A64HelloTcbArea

namespace Spike.Lib.HelloH2CP

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib (FragS Frag)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Rt.PreChild (r1Of)
open Spike.Lib.HelloPreA (clonePcH CloneInvH cloneAtH)
open Spike.Lib.HelloHMid (CloneMidH)
open Spike.Lib.HelloH2Inv (X2H)
open Scc.Cert.Rt.A64 (Lays endOf)

/-- **`hB2_of`'s `hCP` at `CloneMidH`**: a `CloneMidH` state (main at the clone's `svc`, the box `l'` at `b'`)
is inside the level `W` and `X2H` at the twice extended placement and sizes, a `clone` refusal's (`ClH`), and off
the take pc `a` (`hna`), given the level's extra fact `Wc` the child's stack private (`hWc`), the child's stack in
the pool (`hsub`), `CloneInvH` at `CloneMidH`'s states (`hCI`) and main's segment-end facts there (`hSeg`; at the
root `HelloCloneSeg.cloneSegH_of_mid`). -/
theorem hCP_of {L : RuntimeLayout} {F0 : MachineData → Prop}
    {G : Region → (MachineData → Prop) → (Spike.Lib.A64.Flow.AS → Ctl → Prop) → UInt64 → Prop}
    {W : FragS isaLSE2} {Wc : Frag isaLSE2} {a endPc : Int64} {L0 : Lbl} {ls0 : Lsize}
    {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat} {ws : List TermRun.Word}
    (hp : L.prog = SccCode.helloProg) (hsub : (r1Of L.lab).Sub L.Λ.stackPool)
    (hna : clonePcH L ≠ a.toBitVec.toNat)
    (hWc : ∀ s c, Wc s c → Spike.Lib.A64.Flow.Ret0.StackM (r1Of L.lab) s.st.1)
    (hCI : ∀ s c fs, CloneMidH L F0 G W Wc l' b' ws n' s c fs →
      CloneInvH L endPc (Spike.Lib.A64ConsumerA.upd (Spike.Lib.A64ConsumerA.upd L0 l b) l' b') s c [])
    (hSeg : ∀ s c fs, CloneMidH L F0 G W Wc l' b' ws n' s c fs → Spike.Lib.HelloCloneSegD.CloneSegD L endPc s c) :
    ∀ s c fs, CloneMidH L F0 G W Wc l' b' ws n' s c fs →
      (W s c fs ∧ X2H L a endPc (Spike.Lib.A64ConsumerA.upd (Spike.Lib.A64ConsumerA.upd L0 l b) l' b')
        (Spike.Lib.A64ConsumerA.updN (Spike.Lib.A64ConsumerA.updN ls0 l n) l' n') s c fs) ∧
      Spike.Lib.A64.HelloPh.ClH L s ∧ s.st.2 ≠ a := by
  intro s c fs h
  have hci := hCI s c fs h
  have hsg := hSeg s c fs h
  have hx3 := Spike.Lib.HelloTcbArea.x3_of_cloneMidH h
  obtain ⟨t', hpost⟩ := CloneMidH.post h
  obtain ⟨rfl, hW, hWc', R, F, J1, t, sl, me, cA, fr, hB, -, -, -, hsrc, hA, -, -⟩ := h
  have hpS : Lays L.exe SccCode.helloProg L.pfx := hp ▸ L.lays
  have hendS : L.endPc = endOf L.exe SccCode.helloProg L.pfx := by
    show endOf L.exe L.prog L.pfx = _; rw [hp]
  have hpc := Spike.Lib.A64.Flow.HelloWc.wcNSH_clonePc hA
  have hq := Spike.Lib.A64.Flow.HelloWc.wcNSH_cloneAt hA
  have hcode := Spike.Lib.A64.Flow.code_of hpS hendS Spike.Lib.A64.Flow.Worker.Hello.Child.hello_svcIn
    (q := cloneAtH Spike.Lib.A64.Flow.Worker.Hello.Child.pfxM L.exe) rfl
  have hna' : s.st.2 ≠ a := fun e => hna (by rw [← hpc]; unfold pcOf; rw [e])
  obtain ⟨he, hn, -, -, σ, hAb, -, hJ⟩ := hA
  have hx1 : s.st.1.regs.X1.toBitVec = Spike.Lib.A64.Flow.WakeWc.kOf L.lab := by
    rw [hAb.regs]; exact hJ.2.2.1
  refine ⟨⟨hW, fun _ => ⟨hci, fun l'' hc' => ?_, Spike.Lib.A64Consumer.owned_of_stackM hsub (hWc s c hWc'), hx1,
      hsg, hx3⟩,
    fun ha => (hna (by rw [← hpc]; exact ha)).elim⟩,
    ⟨hpc, Scc.Sem.A64.atSvc_of_cellAt ((hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hq]; simp)),
      Spike.Lib.HelloPreA.clone_decode_of_postH hpost⟩, hna'⟩
  obtain ⟨-, -, hc, -⟩ := hsrc
  obtain ⟨-, -, -, -, -, -, -, rfl, -⟩ := hB
  rw [hc] at hc'; simp [TermRun.cst, Promises.TVal.mk0] at hc'; subst hc'
  simp [Spike.Lib.A64ConsumerA.updN]

/-- **`CloneInvH` at `CloneMidH`** (`hCP_of`'s `hCI`; wake's `cloneInv_of_wcNS`) at a placement `lbl` that places
the box `l'` at `b'` (`hl'`), given the box's ghost facts `G` pin `wc_main`'s entry registers (`hG`): `x0 .. x3` the
slice `ws`'s representation (`SlRep`) and `x4` main's id label's place. At the clone's `svc` `wcNSH` puts the
slice's saves in `x9 .. x12`, the cell in `x13` and main's word in `x14` (`FrMGH`: the entry's `x0 .. x4`). -/
theorem cloneInvH_of_mid {L : RuntimeLayout} {F0 : MachineData → Prop}
    {G : Region → (MachineData → Prop) → (Spike.Lib.A64.Flow.AS → Ctl → Prop) → UInt64 → Prop}
    {W : FragS isaLSE2} {Wc : Frag isaLSE2} {lbl : WeakMem.AllocLabel → Option Nat}
    {l' : WeakMem.AllocLabel} {b' n' : Nat} {ws : List TermRun.Word}
    (hl' : lbl l' = some b')
    (hG : ∀ R F J1 t, G R F J1 t → ∀ σe c, J1 σe c →
      Spike.Lib.HelloMainPreSrc.SlRep lbl ws σe.regs.X0.toNat σe.regs.X1.toNat σe.regs.X2.toNat
        σe.regs.X3.toNat ∧ lbl (Spike.Lib.WakeT1.mainTidLbl 2) = some σe.regs.X4.toNat) :
    ∀ s c fs, CloneMidH L F0 G W Wc l' b' ws n' s c fs → CloneInvH L L.endPc lbl s c [] := by
  intro s c fs h
  obtain ⟨t', hpost⟩ := CloneMidH.post h
  obtain ⟨-, -, -, R, F, J1, t, sl, me, cA, fr, -, hGx, ⟨σe, c', hJ, -, hsl, hme⟩, hcA, hsrc, hA, -, -⟩ := h
  obtain ⟨hrep, htid⟩ := hG R F J1 t hGx σe c' hJ
  obtain ⟨-, -, -, -, σ, hAb, -, hN⟩ := hA
  obtain ⟨-, -, -, -, -, -, -, h9, h10, h11, h12, h13, h14, -⟩ := hN
  subst hsl hme
  have e : ∀ {x y : UInt64} {v : BitVec 64}, x = y → y.toBitVec = v → x.toNat = v.toNat := by
    intro x y v hxy hy; subst hxy; rw [← hy]; rfl
  refine ⟨rfl, t', l', ws, hpost, hsrc, ?_, ?_, ?_⟩
  · rw [hl']; congr 1
    show b' = (s.st.1.regs.X13).toNat
    rw [e (congrArg (·.X13) hAb.regs) h13]
    exact hcA.symm
  · rw [htid]; congr 1
    show σe.regs.X4.toNat = (s.st.1.regs.X14).toNat
    rw [e (congrArg (·.X14) hAb.regs) h14]; rfl
  · show Spike.Lib.HelloMainPreSrc.SlRep lbl ws (s.st.1.regs.X9).toNat (s.st.1.regs.X10).toNat
      (s.st.1.regs.X11).toNat (s.st.1.regs.X12).toNat
    rw [e (congrArg (·.X9) hAb.regs) h9, e (congrArg (·.X10) hAb.regs) h10, e (congrArg (·.X11) hAb.regs) h11,
      e (congrArg (·.X12) hAb.regs) h12]
    exact hrep

end Spike.Lib.HelloH2CP

/-- info: 'Spike.Lib.HelloH2CP.hCP_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloH2CP.hCP_of

/-- info: 'Spike.Lib.HelloH2CP.cloneInvH_of_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloH2CP.cloneInvH_of_mid
