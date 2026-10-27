/-
**The emit rows from the node obligations** on the canonical AArch64
target: `EmitA` (`Spike/Lib/A64ConsumerAE.lean`) at `Top := PrintTop` from
`NodesA … (some Ab)` and, at every pair of the fragment at a `write(1, buf,
n)`, the source at `print`'s loop top with a byte left (`PrintSvc`,
`Spike/Lib/PrintSvc.lean`; the per-pair facts' `svc1`).

The fragment's own row at such a pair (`NodesA.out`) is an `Out.emit`: the
cell is an `svc` (`NodesA.svc`, `exec_svc`), and `Out.sys` supports no
`write` to descriptor 1 (`SysOk`). Its frame run and local run stay at the
pair's frames and end at no hold in `printL`'s body
(`frameRun_printSvc`); its controls `Pw j` are cut down to those
(`byteOut_printTop` for the byte steps), the suspended frames placed by
`NodesA.place`.

- `emitA_of_nodes`: the emit rows.
-/
import Spike.Lib.A64ConsumerAE
import Spike.Lib.PrintSvcRun

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.PrintSvc (PrintSvc PrintTop frameRun_printSvc byteOut_printTop)

variable {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {Ab : State → Prop}

/-- **The emit rows from the node obligations**, at `Top := PrintTop`: at
every pair of the fragment at a `write(1, buf, n)` the source is at
`print`'s loop top with a byte left (`hps`, the per-pair facts' `svc1`), and
`printL` is `printLD` (`hd`). -/
theorem emitA_of_nodes (hN : NodesA Λ p μ rd G own ar I (some Ab)) {rS : Range} {Tk : State → Prop}
    (hT : TakePathS Λ p μ I rS Tk) (hd : p.find? (·.name == "printL") = some PrintSrc.printLD)
    (hps : ∀ lbl lsize s c fs, I lbl lsize s c fs → abi.atSys s = true → ∀ b n,
      Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write 1 b n) → PrintSvc c fs) :
    EmitA Λ p I PrintTop := by
  refine ⟨fun lbl lsize s c fs hI hs buf n hdec => ?_⟩
  obtain ⟨imm, sz, hc⟩ := hN.svc _ _ _ _ _ hI hs
  have hsv := hps _ _ _ _ _ hI hs buf n hdec
  have hex := Kraken.Promising.Lower.A64.exec_svc hc
  cases hN.out _ _ _ _ _ hI (hT.off_sys hI hs) with
  | frame s' c' fs' he _ _ => rw [hex] at he; cases he
  | pre c₁ fs₁ hr h =>
    obtain ⟨rfl, -, -⟩ := frameRun_printSvc hd hsv hr
    cases h with
    | silent s' c' he => rw [hex] at he; cases he
    | choice P t he hs' => rw [hex] at he; cases he; exact hs'.elim
    | load _ _ _ _ _ _ _ _ he => rw [hex] at he; cases he
    | store _ _ _ _ _ _ _ _ _ _ _ _ he => rw [hex] at he; cases he
    | rtStore _ _ _ _ _ he => rw [hex] at he; cases he
    | rtLoad _ _ _ _ he => rw [hex] at he; cases he
    | rtRmw _ _ _ _ _ he => rw [hex] at he; cases he
    | holdLoad _ _ _ _ _ _ _ _ he => rw [hex] at he; cases he
    | xchgStore _ _ _ _ _ _ _ _ _ _ _ _ he => rw [hex] at he; cases he
    | ctrRmw _ _ _ _ _ _ _ _ _ _ he => rw [hex] at he; cases he
    | alloc _ _ _ _ _ _ _ _ _ _ _ _ he => rw [hex] at he; cases he
    | sys K call hK _ hd' hok _ =>
      cases hK
      rw [hdec] at hd'
      cases hd'
      exact (hok.2.2.1 1 buf n rfl rfl).elim
    | emit K b' n' Pw Qw hK _ hd' h0 hb hr' _ =>
      cases hK
      rw [hdec] at hd'
      cases hd'
      obtain ⟨c', hlr, hp⟩ := h0
      obtain ⟨-, hh', ht'⟩ := frameRun_printSvc hd hsv (hr.trans (FrameRun.ofLocal hlr _))
      refine ⟨c₁, _, fun j c => Pw j c ∧ c.hold = none ∧ PrintTop c, hr, hsv.1, (hN.place _ _ _ _ _ hI).frames,
        ⟨c', hlr, hp, hh', ht'⟩, ⟨fun j hj c1 h => byteOut_printTop hd (hb j hj c1 h.1), ?_⟩,
        fun j _ c' h => h.2⟩
      exact fun j hj c1 h r hm hok => (hr' j hj c1 h.1 r hm hok).1

end Spike.Lib.A64ConsumerA
