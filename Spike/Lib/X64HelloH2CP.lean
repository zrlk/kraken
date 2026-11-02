/-
**main at the clone in `h2`'s invariant** (x86-64; the twin of `Spike/Lib/A64HelloH2CP.lean`, the hello twin of
the first three bullets of `Spike/Lib/X64WakeBoxW.lean`'s `hB_box`): `X64HelloH2Box.hB2_of`'s `hCP` at
`CP := X64HelloHMid.CloneMidH … l' b' n'` (the box's label `l'` at `b'`), `Cl := X64.HelloPh.ClH L`.

At a `CloneMidH` state main is at the clone's `syscall` (`wcNSH_clonePc`), a system call (`hello_svcIn`) that
decodes to a `clone` (`clone_decode_of_postH`), so it is `ClH`'s and off the take pc (`hna`); inside the level (`W`
at no frames); `X2H`'s clone clause holds: `%rsi` is `kOf` and `%r8` the second TCB (`wcNSH`), `c`'s label is the
box `l'` of `n' = 1` cell (`SpawnSrcH`, `BoxPureH`), the child's stack owned from the level's extra fact at the
clone (`Wc`, `StackM r1Of` by the hat's late frame condition, `owned_of_stackM`), and `CloneInvH` (`hCI`); `X2H`'s
take clause is vacuous.

- `cloneInvH_of_mid`: `hCI` from `CloneMidH` at a placement placing the box, given `G` pins the entry registers.
- `hCP_of`: `hCP` from `CloneMidH`, given `CloneInvH` there (`hCI`), main's segment-end facts (`hSeg`) and the
  parent's saved frame pointer at the clone frame (`hFp`).

Unlike AArch64, `wcNSH` keeps the slice's words in `%r12`, `%rbx`, `%r13`, `%r14`, the cell in `%r15` and main's
word in `%r9` (from `wc_main`'s entry `%rdi`, `%rsi`, `%rdx`, `%rcx`, `%r8`: `FrMGH`), and `X2H`'s second-TCB
clause (`%r8 = tH`) is read off `wcNSH` directly (AArch64: `HelloTcbArea.x3_of_cloneMidH`).
-/
import Spike.Lib.X64HelloH2Box
import Spike.Lib.X64HelloClH
import Spike.Lib.X64HelloChildAt
import Spike.Lib.X64OwnedStackM
import Spike.Lib.X64HelloHMid
import Spike.Lib.X64HelloParent

namespace Spike.Lib.X64HelloH2CP

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (FragS Frag Region)
open Spike.Lib.X64 (AS CodeAt)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64HelloPreA (clonePcH CloneInvH cloneAtH)
open Spike.Lib.X64HelloHMid (CloneMidH)
open Spike.Lib.X64HelloH2Inv (X2H)
open Spike.Lib.X64.WakePh.WcClone (svcB)
open Spike.Lib.X64WakeSrcDefs (mainTidLbl)
open Scc.Cert.Rt.X64 (Lays endOf codeAt_blockAt_lays)

/-- **`hB2_of`'s `hCP` at `CloneMidH`**: a `CloneMidH` state (main at the clone's `syscall`, the box `l'` at `b'`)
is inside the level `W` and `X2H` at the twice extended placement and sizes, a `clone` refusal's (`ClH`), and off
the take pc `a` (`hna`), given the level's extra fact `Wc` the child's stack private (`hWc`), the child's stack in
the pool (`hsub`), `CloneInvH` at `CloneMidH`'s states (`hCI`), main's segment-end facts there (`hSeg`) and the
parent's saved frame pointer at the clone frame's slot `80` (`hFp`). -/
theorem hCP_of {L : RuntimeLayout} {F0 : MachineData → Prop}
    {G : Region → (MachineData → Prop) → (AS → Ctl → Prop) → UInt64 → Prop}
    {W : FragS isa} {Wc : Frag isa} {a endPc : Int64} {L0 : Lbl} {ls0 : Lsize}
    {l : WeakMem.AllocLabel} {b n : Nat} {l' : WeakMem.AllocLabel} {b' n' : Nat} {ws : List TermRun.Word}
    (hp : L.prog = SccCode.helloCells) (hsub : (r1Of L.lab).Sub L.Λ.stackPool)
    (hna : clonePcH L ≠ a.toBitVec.toNat)
    (hWc : ∀ s c, Wc s c → Spike.Lib.X64.Flow.Ret0.StackM (r1Of L.lab) s.st.1)
    (hCI : ∀ s c fs, CloneMidH L F0 G W Wc l' b' ws n' s c fs →
      CloneInvH L endPc (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64ConsumerA.upd L0 l b) l' b') s c [])
    (hSeg : ∀ s c fs, CloneMidH L F0 G W Wc l' b' ws n' s c fs →
      Spike.Lib.X64HelloCloneSegD.CloneSegD L endPc s c)
    (hFp : ∀ s c fs, CloneMidH L F0 G W Wc l' b' ws n' s c fs → ∀ (Rm : Region) (F₂ : MachineData → Prop)
      (cA fp ra tp : BitVec 64),
      Spike.Lib.X64.At L.exe endPc ⟨Rm.base, -128, 40⟩ F₂
        ⟨cloneAtH L.exe, Spike.Lib.X64.Flow.Worker.Hello.Parent.oP,
          Spike.Lib.X64.Flow.Worker.Hello.Parent.JS c cA fp ra tp⟩ s c →
        fp = (⟨Rm.base, -128, 40⟩ : Region).addr 80) :
    ∀ s c fs, CloneMidH L F0 G W Wc l' b' ws n' s c fs →
      (W s c fs ∧ X2H L a endPc (Spike.Lib.X64ConsumerA.upd (Spike.Lib.X64ConsumerA.upd L0 l b) l' b')
        (Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64ConsumerA.updN ls0 l n) l' n') s c fs) ∧
      Spike.Lib.X64.HelloPh.ClH L s ∧ s.st.2 ≠ a := by
  intro s c fs h
  have hci := hCI s c fs h
  have hsg := hSeg s c fs h
  have hfp := hFp s c fs h
  obtain ⟨t', hpost⟩ := CloneMidH.post h
  obtain ⟨rfl, hW, hWc', R, F, J1, t, sl, me, cA, fr, hB, -, -, -, hsrc, hA, -, -⟩ := h
  have hpS : Lays L.exe SccCode.helloCells L.pfx := hp ▸ L.lays
  have hendS : L.endPc = endOf L.exe SccCode.helloCells L.pfx := by
    show endOf L.exe L.prog L.pfx = _; rw [hp]
  have hpc := Spike.Lib.X64.Flow.HelloWc.wcNSH_clonePc hA
  have hq := Spike.Lib.X64.Flow.HelloWc.wcNSH_cloneAt hA
  have hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc → CodeAt s (cloneAtH L.exe) svcB :=
    fun s he hn => codeAt_blockAt_lays hpS he (hn.trans hendS) Spike.Lib.X64.Flow.Worker.Hello.Child.hello_svcIn
  have hna' : s.st.2 ≠ a := fun e => hna (by rw [← hpc]; unfold pcOf; rw [e])
  obtain ⟨he, hn, -, -, σ, hAb, -, ⟨-, -, -, -, -, -, -, hsi, h8, -⟩, -⟩ := hA
  have hx1 : s.st.1.regs.get64 .rsi = Spike.Lib.X64.Flow.WakeWc.kOf L.lab := by rw [hAb.regs]; exact hsi
  have hx3 : s.st.1.regs.get64 .r8 = Spike.Lib.X64.Flow.HelloWc.tH L.lab := by rw [hAb.regs]; exact h8
  refine ⟨⟨hW, fun _ => ⟨hci, fun l'' hc' => ?_, Spike.Lib.X64Consumer.owned_of_stackM hsub (hWc s c hWc'), hx1,
      hsg, hx3, hfp⟩,
    fun ha => (hna (by rw [← hpc]; exact ha)).elim⟩,
    ⟨hpc, Scc.Sem.X64.atSyscall_of_cellAt ((hcode s he hn).cell0 rfl rfl hq),
      Spike.Lib.X64HelloPreA.clone_decode_of_postH hpost⟩, hna'⟩
  obtain ⟨-, -, hc, -⟩ := hsrc
  obtain ⟨-, -, -, -, -, -, -, rfl, -⟩ := hB
  rw [hc] at hc'; simp [TermRun.cst, Promises.TVal.mk0] at hc'; subst hc'
  simp [Spike.Lib.X64ConsumerA.updN]

/-- **`CloneInvH` at `CloneMidH`** (`hCP_of`'s `hCI`; wake's `cloneInv_of_wcNS`) at a placement `lbl` that places
the box `l'` at `b'` (`hl'`), given the box's ghost facts `G` pin `wc_main`'s entry registers (`hG`): `%rdi`,
`%rsi`, `%rdx`, `%rcx` the slice `ws`'s representation (`SlRep`) and `%r8` main's id label's place. At the clone's
`syscall` `wcNSH` puts the slice's saves in `%r12`, `%rbx`, `%r13`, `%r14`, the cell in `%r15` and main's word in
`%r9` (`FrMGH`: the entry's `%rdi .. %rcx`, `%r8`). -/
theorem cloneInvH_of_mid {L : RuntimeLayout} {F0 : MachineData → Prop}
    {G : Region → (MachineData → Prop) → (AS → Ctl → Prop) → UInt64 → Prop}
    {W : FragS isa} {Wc : Frag isa} {lbl : WeakMem.AllocLabel → Option Nat}
    {l' : WeakMem.AllocLabel} {b' n' : Nat} {ws : List TermRun.Word}
    (hl' : lbl l' = some b')
    (hG : ∀ R F J1 t, G R F J1 t → ∀ σe c, J1 σe c →
      Spike.Lib.X64HelloMainPreSrc.SlRep lbl ws σe.regs.rdi.toNat σe.regs.rsi.toNat σe.regs.rdx.toNat
        σe.regs.rcx.toNat ∧ lbl (mainTidLbl 2) = some σe.regs.r8.toNat) :
    ∀ s c fs, CloneMidH L F0 G W Wc l' b' ws n' s c fs → CloneInvH L L.endPc lbl s c [] := by
  intro s c fs h
  obtain ⟨t', hpost⟩ := CloneMidH.post h
  obtain ⟨-, -, -, R, F, J1, t, sl, me, cA, fr, -, hGx, ⟨σe, c', hJ, -, hsl, hme⟩, hcA, hsrc, hA, -, -⟩ := h
  obtain ⟨hrep, htid⟩ := hG R F J1 t hGx σe c' hJ
  obtain ⟨-, -, -, -, σ, hAb, -, ⟨-, h12, hbx, h13, h14, h15, h9, -⟩, -⟩ := hA
  subst hsl hme
  have e : ∀ {x : Reg64s → BitVec 64} {v : BitVec 64}, x σ.regs = v → (x s.st.1.regs).toNat = v.toNat := by
    intro x v hx; rw [hAb.regs, hx]
  refine ⟨rfl, t', l', ws, hpost, hsrc, ?_, ?_, ?_⟩
  · rw [hl', e (x := fun r => r.get64 .r15) h15, hcA]
  · rw [htid, e (x := fun r => r.get64 .r9) h9]; rfl
  · rw [e (x := fun r => r.get64 .r12) h12, e (x := fun r => r.get64 .rbx) hbx,
      e (x := fun r => r.get64 .r13) h13, e (x := fun r => r.get64 .r14) h14]
    exact hrep

end Spike.Lib.X64HelloH2CP

/-- info: 'Spike.Lib.X64HelloH2CP.hCP_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloH2CP.hCP_of

/-- info: 'Spike.Lib.X64HelloH2CP.cloneInvH_of_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloH2CP.cloneInvH_of_mid
