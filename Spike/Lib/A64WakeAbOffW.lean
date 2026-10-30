/-
**wake.w's worker off the `writeErr` and `threads` abort exits** (AArch64): `AbOffL lab` (`Spike/Lib/A64AbOffLDef.lean`, the
pc is none of the two abort exit calls and the two transfer sites) at every
node of the child's segments, decided per pc on the listing (`abChk`,
`abOff_at`, `Spike/Lib/A64WakeAbOffL.lean`), and with `wakePass`
(`Spike/Lib/A64WakePass.lean`) the fragment `wakeZ lab` for
`seg_childPreNN` at `Z := wakeZ`. A worker side whose invariant lies inside
`wakeZ` is off the abort sites at the placed layout's marks: the
`WakeAssembly` checklist item `hab1` (`hab1_of`). The listing is wake.w's
certificate (`Spike/Test/Cert/A64WakeCert.s`).

- `wakeZ lab`: `wakePass ∧ AbOffL lab`.
- `nodeZ_and`, `thrZ_and`: the facts at the nodes combine.
- `nodeZ_ab`, `pro_ab`: a node (prologue) with a decided pc check.
- `head_ab`, `wk_ab`, `unpk_ab`, `tail_ab`: each function's nodes.
- `thrZ_ab`, `cZ_ab`: `AbOffL` at every node of the thread worker's run and
  of the child's stub.
- `childThrZW`, `cZW`: `seg_childPreNN`'s premises at `Z := wakeZ lab`.
- `marks_target`: the canonical target's marks at any hooks and entry are
  `PhRec.μ L`; `hab1_of`: `hab1` from `wakeZ` at `RuntimeLayout.ofPlaceW`.
-/
import Spike.Lib.A64WakePass
import Spike.Lib.A64WakeAbOffL
import Spike.Lib.A64AbOffL
import Spike.Lib.PlaceWRt

namespace Spike.Lib.A64.Flow.Worker.Wake.AbOffW

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays blockAt labelGap label_labelGap labelIdx run)
open Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Worker.Wake
open Spike.Lib.A64.Flow.Worker.Wake.Labels (ThrZ thrJ thrJE wcJE)
open Spike.Lib.A64.Flow.Worker.Wake.Child (cN childN childJ cLen pfxM kidC)
open Spike.Lib.A64.Flow.Worker.Wake.Split (workerTy workerRest wc1)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Flow.Worker.Wake.Pass (wakePass)
open Spike.Lib.A64.Flow.Worker.Wake.AbOffAt (abChk abOff_at)
open Spike.Lib.A64AbOffL (AbOffL)

/-- **The worker's fragment**: the store point on both sides agrees
(`wakePass`) and the pc is off the abort exits and transfer sites. -/
def wakeZ (lab : Label → Int64) : Frag isaLSE2 := fun s c => wakePass s c ∧ AbOffL lab s c

/-- Facts at a node combine. -/
theorem nodeZ_and {Z Z' : Frag isaLSE2} {exe : _root_.Executable} {n : ND} {len : Nat}
    (h : NodeZ Z exe n len) (h' : NodeZ Z' exe n len) : NodeZ (fun s c => Z s c ∧ Z' s c) exe n len :=
  fun s σ c k hk he hs hJ => ⟨h s σ c k hk he hs hJ, h' s σ c k hk he hs hJ⟩

/-- Facts at the thread worker's nodes combine. -/
theorem thrZ_and {Z Z' : Frag isaLSE2} {exe : _root_.Executable} {c0 c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64}
    (h : ThrZ Z exe c0 c1 c2 c3 A B tp sp0) (h' : ThrZ Z' exe c0 c1 c2 c3 A B tp sp0) :
    ThrZ (fun s c => Z s c ∧ Z' s c) exe c0 c1 c2 c3 A B tp sp0 where
  pro s σ c k hk he hs hJ := ⟨h.pro s σ c k hk he hs hJ, h'.pro s σ c k hk he hs hJ⟩
  head i := nodeZ_and (h.head i) (h'.head i)
  wpro x29 ra s σ c k hk he hs hJ := ⟨h.wpro x29 ra s σ c k hk he hs hJ, h'.wpro x29 ra s σ c k hk he hs hJ⟩
  wk x29 ra i := nodeZ_and (h.wk x29 ra i) (h'.wk x29 ra i)
  unpk x29 ra i := nodeZ_and (h.unpk x29 ra i) (h'.unpk x29 ra i)
  tail i := nodeZ_and (h.tail i) (h'.tail i)

section Inst

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe wakeProg kp)
include hp

/-- **`AbOffL` at a node** at the instructions `k0 ..` after `l`, decided. -/
theorem nodeZ_ab {n : ND} {len : Nat} {l : Label} {k0 : Nat}
    (hpc : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k0))
    (hchk : abChk l k0 len = true) : NodeZ (AbOffL (_root_.Executable.labels exe).label) exe n len :=
  fun _ _ _ _ hk he hs _ => abOff_at hp hchk hk he (hpc ▸ hs)

/-- **`AbOffL` at a prologue** (`fn`'s label is its stack check's, `sc`). -/
theorem pro_ab {fn sc : Label} (hg : labelGap wakeProg fn sc 0 = true) (hchk : abChk sc 0 11 = true)
    {J : AS → Ctl → Prop} :
    ∀ (s : State) σ c (k : Nat), k < 11 → s.exe = exe →
      s.st.2 = (_root_.Executable.labels exe).label fn + Int64.ofNat (4 * k) → J σ c →
        AbOffL (_root_.Executable.labels exe).label s c := by
  intro s σ c k hk he hs _
  refine abOff_at hp hchk hk he ?_
  rw [hs, label_labelGap hp hg]
  simp only [ofNat4_zero]

/-- Closes `nodeZ_ab`'s side goals: the node's pc, the decided check. -/
local macro "za" : tactic =>
  `(tactic| first
    | (simp only [Unpark.N, Unpark.pcSvc, WkTailW.N, WkTailW.pcBl, ThrTailW.N, ThrHeadW.tN, cN, childN,
        ofNat4_succ, ofNat4_zero]; done)
    | decide +kernel)

/-- `AbOffL` at `scc_rt_thr_worker`'s head. -/
theorem head_ab {c0 c1 : Ctl} {A B tp sp0 : BitVec 64} (i : ThrHeadW.TN) :
    NodeZ (AbOffL (_root_.Executable.labels exe).label) exe
      (ThrHeadW.tN ThrTailW.pfx0 (_root_.Executable.labels exe).label (thrJ c0 A B tp sp0)
        (fun _ c => c = c1) i) (ThrHeadW.lenN i) := by
  cases i
  · refine nodeZ_ab hp (l := (ThrTailW.pfx0 ++ ".0_entry")) (k0 := 0) ?_ ?_ <;> za
  · exact Pass.nodeZ_nil

/-- `AbOffL` at `wc_worker`'s nodes. -/
theorem wk_ab {c1 c2 c3 : Ctl} {A B x29 ra tp : BitVec 64} (i : WkTailW.PN) :
    NodeZ (AbOffL (_root_.Executable.labels exe).label) exe
      (WkTailW.N WkTailW.pfx0 (_root_.Executable.labels exe).label c1 c2 c3 A B x29 ra tp i) (WkTailW.lenN i) := by
  cases i
  · refine nodeZ_ab hp (l := (WkTailW.pfx0 ++ ".0_entry")) (k0 := 0) ?_ ?_ <;> za
  · refine nodeZ_ab hp (l := (WkTailW.pfx0 ++ ".0_entry")) (k0 := 2) ?_ ?_ <;> za
  · refine nodeZ_ab hp (l := (WkTailW.pfx0 ++ ".0_entry")) (k0 := 3) ?_ ?_ <;> za
  · refine nodeZ_ab hp (l := (WkTailW.pfx0 ++ ".0_entry")) (k0 := 4) ?_ ?_ <;> za
  · exact Pass.nodeZ_nil
  · refine nodeZ_ab hp (l := (WkTailW.pfx0 ++ ".sp1")) (k0 := 0) ?_ ?_ <;> za

/-- `AbOffL` at `scc_rt_unpark`'s nodes. -/
theorem unpk_ab {c2 c3 : Ctl} {B x29 ra tp : BitVec 64} (i : Unpark.PN) :
    NodeZ (AbOffL (_root_.Executable.labels exe).label) exe
      (Unpark.N (_root_.Executable.labels exe).label c2 c3 B x29 ra tp i) (Unpark.lenN i) := by
  cases i
  · refine nodeZ_ab hp (l := "scc_rt_unpark") (k0 := 0) ?_ ?_ <;> za
  · refine nodeZ_ab hp (l := ".L11_scc_rt_unpark.0_entry") (k0 := 0) ?_ ?_ <;> za
  · refine nodeZ_ab hp (l := ".L11_scc_rt_unpark.0_entry") (k0 := 3) ?_ ?_ <;> za
  · refine nodeZ_ab hp (l := ".L11_scc_rt_unpark.0_entry") (k0 := 4) ?_ ?_ <;> za
  · refine nodeZ_ab hp (l := ".L11_scc_rt_unpark.0_entry") (k0 := 9) ?_ ?_ <;> za
  · refine nodeZ_ab hp (l := ".L11_scc_rt_unpark.1_wake") (k0 := 0) ?_ ?_ <;> za
  · refine nodeZ_ab hp (l := ".L11_scc_rt_unpark.1_wake") (k0 := 11) ?_ ?_ <;> za
  · refine nodeZ_ab hp (l := ".L11_scc_rt_unpark.1_wake") (k0 := 12) ?_ ?_ <;> za
  · refine nodeZ_ab hp (l := ".L11_scc_rt_unpark.2_done") (k0 := 0) ?_ ?_ <;> za

/-- `AbOffL` at `scc_rt_thr_worker`'s tail. -/
theorem tail_ab {c3 : Ctl} {tp : BitVec 64} (i : ThrTailW.PN) :
    NodeZ (AbOffL (_root_.Executable.labels exe).label) exe
      (ThrTailW.N ThrTailW.pfx0 (_root_.Executable.labels exe).label c3 tp i) (ThrTailW.lenN i) := by
  cases i
  · refine nodeZ_ab hp (l := (ThrTailW.pfx0 ++ ".sp0")) (k0 := 0) ?_ ?_ <;> za
  · refine nodeZ_ab hp (l := (ThrTailW.pfx0 ++ ".sp0")) (k0 := 5) ?_ ?_ <;> za
  · refine nodeZ_ab hp (l := (ThrTailW.pfx0 ++ ".sp0")) (k0 := 6) ?_ ?_ <;> za
  · refine nodeZ_ab hp (l := (ThrTailW.pfx0 ++ ".sp0")) (k0 := 8) ?_ ?_ <;> za

/-- **`AbOffL` at every node of the thread worker's run.** -/
theorem thrZ_ab {c0 c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64} :
    ThrZ (AbOffL (_root_.Executable.labels exe).label) exe c0 c1 c2 c3 A B tp sp0 where
  pro := pro_ab hp (sc := ThrTailW.pfx0 ++ ".stack_check") (by decide +kernel) (by decide +kernel)
  head := head_ab hp
  wpro _ _ := pro_ab hp (sc := WkTailW.pfx0 ++ ".stack_check") (by decide +kernel) (by decide +kernel)
  wk _ _ := wk_ab hp
  unpk _ _ := unpk_ab hp
  tail := tail_ab hp

/-- **`AbOffL` at the child's stub.** -/
theorem cZ_ab {cW : Ctl} {A B tp sp0 : BitVec 64} :
    ∀ i, NodeZ (AbOffL (_root_.Executable.labels exe).label) exe
      (cN pfxM (_root_.Executable.labels exe).label cW A B tp sp0 i) (cLen i) := by
  intro i
  cases i
  · refine nodeZ_ab hp (l := (pfxM ++ ".sp6")) (k0 := 14) ?_ ?_ <;> za
  · refine nodeZ_ab hp (l := (pfxM ++ ".child9")) (k0 := 0) ?_ ?_ <;> za

/-- **`wakeZ` at the spawned child's nodes** (`seg_childPreNN`'s `ThrZ`
premise at `Z := wakeZ`). -/
theorem childThrZW (T : Ty) (w1 w2 : TermRun.Word) (A B tp sp0 : BitVec 64) :
    ThrZ (wakeZ (_root_.Executable.labels exe).label) exe (kidC T w1 w2) (wc1 workerTy w1 w2)
      ⟨.let_ "w" (.ext .unpark (.var "j")) (.ret .unit), ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
      ⟨.ret .unit, ("w", ExtName.unpark.sig.2, []) :: ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
      A B tp sp0 :=
  thrZ_and (Pass.childThrZ hp T w1 w2 A B tp sp0) (thrZ_ab hp)

/-- **`wakeZ` at the child's stub** (`seg_childPreNN`'s stub premise at
`Z := wakeZ`). -/
theorem cZW (T : Ty) (w1 w2 : TermRun.Word) {A B tp sp0 : BitVec 64} :
    ∀ i, NodeZ (wakeZ (_root_.Executable.labels exe).label) exe
      (cN pfxM (_root_.Executable.labels exe).label (kidC T w1 w2) A B tp sp0 i) (cLen i) :=
  fun i => nodeZ_and (Pass.cZ_pass hp (Pass.kidC_not T w1 w2) i) (cZ_ab hp i)

end Inst

/-! ## `hab1` -/

open Spike.Lib.A64.Rt (RuntimeLayout)

/-- **The canonical target's marks** at any hooks and entry, of a text
parsing to the layout's program (`hpa`), are the record's (`PhRec.marks_eq`
at any `H`, `E`). -/
theorem marks_target (L : RuntimeLayout) {H : Scc.Sem.Hooks isaLSE2} {E : Scc.Sem.Entry} {asm : String}
    (hpa : Scc.Sem.A64.textProgram asm = .ok L.prog) :
    (Scc.Sem.A64.target H E).marks asm L.Λ = Spike.Lib.A64.PhRec.μ L := by
  have hr := Scc.Sem.A64.resolve_of_parsed H E L.Λ hpa
  unfold Scc.Sem.Target.marks Spike.Lib.A64.PhRec.μ
  congr 1
  · funext k; exact hr _
  · funext k; exact hr _

/-- **`hab1`** (`WakeAssembly.wake_obligations`): at the layout of a placed
output, a worker relation whose states are `wakeZ` of the layout's labels
(`hZ`, from `side_z` at `Z := wakeZ`) puts the worker off the `writeErr` and
`threads` abort sites of the loaded program's marks. -/
theorem hab1_of {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (h : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    {H : Scc.Sem.Hooks isaLSE2} {E : Scc.Sem.Entry} {asm : String}
    (hpa : Scc.Sem.A64.textProgram asm = .ok o.prog) {ι : Type}
    {PT1 : ι → Memory → WeakMem.Memory → Thread isaLSE2 → TermRun.TTh → Prop}
    (hZ : ∀ w tm sm t1 s1, PT1 w tm sm t1 s1 →
      ∃ c, wakeZ (RuntimeLayout.ofPlaceW h i).lab t1.st c) :
    ∀ w tm sm t1 s1, PT1 w tm sm t1 s1 → ∀ k a,
      ((Scc.Sem.A64.target H E).marks asm (RuntimeLayout.ofPlaceW h i).Λ).abortAt k = some a →
        Scc.Sem.A64.pcOf t1.st = a → k ≠ .writeErr ∧ k ≠ .threads := by
  intro w tm sm t1 s1 hP k a ha hpc
  obtain ⟨c, -, hL⟩ := hZ w tm sm t1 s1 hP
  rw [marks_target (RuntimeLayout.ofPlaceW h i) hpa] at ha
  exact Spike.Lib.A64AbOffL.abOff_of_L_ofPlaceOK h i hL k a ha hpc

/-- info: 'Spike.Lib.A64.Flow.Worker.Wake.AbOffW.cZW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cZW

/-- info: 'Spike.Lib.A64.Flow.Worker.Wake.AbOffW.childThrZW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms childThrZW

/-- info: 'Spike.Lib.A64.Flow.Worker.Wake.AbOffW.hab1_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hab1_of

end Spike.Lib.A64.Flow.Worker.Wake.AbOffW
