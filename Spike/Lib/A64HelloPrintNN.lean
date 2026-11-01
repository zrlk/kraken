/-
**hello.w's `scc_rt_print` off the transfer sites** (`WCompatH.noSite`/`sysOkH`, AArch64): `PrintF.FA.seg_printFA`,
`PrintF.FA.hsvc_of_emitT` and `PrintF.printF_callT`
(`Spike/Lib/A64PrintF.lean`) over `SegTC (NNZP Sy exe endPc Z)`
(`Spike/Lib/A64HelloNN.lean`): every state of their hidden invariants at a
cell other than a `nop`, its system call in `Sy`. print's one system call is
its `write` to fd 1 (`SysW1`, `hsvc_of_emitTNN`); its block nodes have no
`svc` (`notNop`), so any `Sy` holds there. `NNZP.toH` takes `SysW1` to
hello's `NNZH`.

The proofs are the originals' with the leaves `seg_ndNNPA`, `dmb_ndNNPA`,
`step_ndNNP`/`nodeW_nnzPSvcA` and wake's `call_ndTS`. Each segment keeps `Z`
at its nodes' states, given per node as
`NodeZA Z exe endPc R F ((N i).withTp tp) (blkN i)` (`hZ`; for the call, in
every callee region and at every realizable call state;
`NodeZ.toAOf … (lenN_eq i)` from a `NodeZ`).

- `PrintF.FA.lenN`, `PrintF.FA.blkN`, `PrintF.FA.lenN_eq`: the nodes' block
  lengths and blocks.
- `PrintF.FA.seg_printFANN`: the function, its `write` a given node.
- `PrintF.FA.hsvc_of_emitTNN`: that node from the output row, inside
  `NNZP SysW1`.
- `PrintF.FA.seg_printFAH`: the two, inside hello's `NNZH`.
- `PrintF.printF_callTNN`: a call of it.
-/
import Spike.Lib.A64PrintF
import Spike.Lib.A64HelloNN

set_option linter.unusedSimpArgs false

namespace Spike.Lib.A64.Flow.Worker.PrintF

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow

namespace FA

open Spike.Lib.A64.Print hiding N E JI PN Code pcSvc PrintW
open Spike.Lib.A64.PrintA hiding N E JI pcSvc PrintAW
open Scc.Sem.Kernel (writeRefused results)
open Kraken.Promising.Lower.A64

/-- Each node's block length (`1` at the fence and the `svc`), the `len` of
its `NodeZ` obligation. -/
def lenN : PN → Nat
  | .e => Print.b0.length | .n1 => Print.b1.length | .loop => Print.b2.length | .n3 => Print.b3.length
  | .fence => 1 | .write => Print.b4.length | .svc => 1 | .n5 => Print.b5.length | .n6 => Print.b6.length
  | .n7 => Print.b7.length | .chk2 => Print.b8.length | .n9 => Print.b9.length | .n10 => Print.b10.length
  | .chk3 => Print.b11.length | .n12 => Print.b12.length | .adv => Print.b13.length
  | .fail => Print.b14.length | .done => Print.b16.length

/-- Each node's block (the instruction at the fence and the `svc`), the
`blk` of its `NodeZA` obligation. -/
def blkN : PN → List Directive
  | .e => Print.b0 | .n1 => Print.b1 | .loop => Print.b2 | .n3 => Print.b3
  | .fence => bF | .write => Print.b4 | .svc => [svcDir] | .n5 => Print.b5 | .n6 => Print.b6
  | .n7 => Print.b7 | .chk2 => Print.b8 | .n9 => Print.b9 | .n10 => Print.b10
  | .chk3 => Print.b11 | .n12 => Print.b12 | .adv => Print.b13
  | .fail => Print.b14 | .done => Print.b16

theorem lenN_eq (i : PN) : lenN i = (blkN i).length := by cases i <;> rfl

section ProofNN

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
  {x29 ra buf0 : BitVec 64} {len0 : Nat} {P Q : Nat → Ctl → Prop} {tp : UInt64}
  {Sy : Scc.Sem.Kernel.Call → Prop} {Z : Frag isaLSE2}

set_option hygiene false in
/-- A block node with the thread pointer off the transfer sites: the block,
its `okBlk`, its code; the edge (without the thread pointer) is left, the
invariant in `hJ`. -/
local macro "pnode " b:ident ok:ident f:ident : tactic =>
  `(tactic| (refine (seg_ndNNPA (by simp [$b:ident]) $ok (by simp [$b:ident, notNop]) hF hR hal hlo hhi
    (fun s he hn => hcode.$f s he hn) (fun σ c hJt => ⟨c, .refl c,
      lands_withTp (by rw [arun_tpidr]; exact hJt.2) ?_⟩) (hZ _)); have hJ := hJt.1; dsimp only [ND.withTp]))

set_option maxHeartbeats 1000000 in
/-- **`seg_printFA` off the transfer sites** (`hsvc` over
`SegTC (NNZP Sy …)`). -/
theorem seg_printFANN (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48)
    (hhi : 0 ≤ R.hi) (hlen : len0 < 2 ^ 63) (hcode : PrintF.Code c0 x29 ra exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L9_scc_rt_print.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 4 + 4 + 4 + 4 + 4 + 4)
    (hsvc : SegTC (NNZP Sy exe endPc Z) p lbl ms
      (At exe endPc R F ((N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc).withTp tp))
      (At exe endPc R F ((N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .n5).withTp tp)))
    (hZ : ∀ i, NodeZA Z exe endPc R F ((N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q i).withTp tp)
      (blkN i)) :
    SegTC (NNZP Sy exe endPc Z) p lbl ms
      (At exe endPc R F ((N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .e).withTp tp))
      (fun s c => ∃ x, At exe endPc R F
        ((PrintA.E (_root_.Executable.labels exe).label x29 ra len0 P Q x).withTp tp) s c) := by
  have hl64 : len0 < 2 ^ 64 := by omega
  refine fn_segTS (N := fun i => (N _ x29 ra buf0 len0 P Q i).withTp tp)
    (E := fun x => (PrintA.E _ x29 ra len0 P Q x).withTp tp) (fun i => ?_) PN.e
  cases i
  case svc => exact hsvc.mono_post fun _ _ h => .inl ⟨PN.n5, h⟩
  case e =>
    pnode Print.b0 Print.b0_ok e; rw [N, PrintA.N, Print.b0_run]; hit PN.n1
    obtain ⟨hP, h29, h30, h0, h1⟩ := hJ
    exact ⟨0, ⟨by simp [Spike.Lib.upd_apply, h29], by simp [Spike.Lib.upd_apply, h30],
      by simp [Spike.Lib.upd_apply, h0], by simp [Spike.Lib.upd_apply, h1], Nat.zero_le _⟩, hP⟩
  case n1 => pnode Print.b1 Print.b1_ok n1; rw [N, PrintA.N, Print.b1_run]; hit PN.loop; exact hJ
  case loop =>
    pnode Print.b2 Print.b2_ok loop; rw [N, PrintA.N, Print.b2_run]
    obtain ⟨k, ⟨h16, h8, h48, h40, hk⟩, hP⟩ := hJ
    simp only [subs0_z, h40]
    by_cases hz : k = len0
    · subst hz
      simp only [Nat.sub_self, decide_true, ite_true]
      hit PN.done
      exact ⟨h16, h8, hP⟩
    · have hz' : ¬ BitVec.ofNat 64 (len0 - k) = 0#64 := fun h => hz ((len_zero hl64 hk).1 h)
      simp only [hz', decide_false, Bool.false_eq_true, ite_false]
      hit PN.n3
      exact ⟨k, ⟨h16, h8, h48, h40, hk⟩, by omega, hP⟩
  case n3 => pnode Print.b3 Print.b3_ok n3; rw [N, PrintA.N, Print.b3_run]; hit PN.fence; exact hJ
  case fence =>
    refine dmb_ndNNPA (fun s he hn => hcode.fence s he hn) (fun σ c hJt => lands_withTp hJt.2 ?_) (hZ .fence).toW
    hit PN.write; exact hJt.1
  case write =>
    pnode Print.b4 Print.b4_ok write; rw [N, Print.b4_run]; hit PN.svc
    refine ⟨hJ, ?_⟩
    simp
  case n5 =>
    pnode Print.b5 Print.b5_ok n5; rw [N, Print.b5_run]; hit PN.n6
    obtain ⟨k, ⟨h16, h8, h48, h40, hk⟩, hr⟩ := hJ
    refine ⟨⟨k, ⟨?_, ?_, ?_, ?_, hk⟩, ?_⟩, ?_⟩
    · simp [Spike.Lib.upd_apply, h16]
    · simp [Spike.Lib.upd_apply, h8]
    · simp [Spike.Lib.upd_apply, h48]
    · simp [Spike.Lib.upd_apply, h40]
    · simpa [Spike.Lib.upd_apply] using hr
    · simp only [Spike.Lib.upd_apply, ite_true]
  case n6 =>
    pnode Print.b6 Print.b6_ok n6; rw [N, Print.b6_run]
    obtain ⟨⟨k, hL, hr⟩, hs⟩ := hJ
    simp only [hs, subs_z]
    by_cases hz : σ.slot (-32) = C4
    · simp only [hz, decide_true, ite_true]
      hit PN.loop
      refine ⟨k, hL, ?_⟩
      rcases hr with ⟨-, hP⟩ | ⟨h11, -⟩ | ⟨h0, hle, -⟩ | ⟨hw, -⟩
      · exact hP
      · rw [hz] at h11; exact absurd h11 (by decide)
      · rw [hz] at hle; have := hL.2.2.2.2; simp only [C4, BitVec.toNat_ofNat] at hle; omega
      · exact absurd hz (refused_ne4 hw)
    · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
      hit PN.n7
      refine ⟨k, hL, ?_⟩
      rcases hr with ⟨h4, -⟩ | h
      · exact absurd h4 hz
      · exact h
  case n7 => pnode Print.b7 Print.b7_ok n7; rw [N, Print.b7_run]; hit PN.chk2; exact hJ
  case chk2 =>
    pnode Print.b8 Print.b8_ok chk2; rw [N, PrintA.N, Print.b8_run]; hit PN.n9
    exact ⟨hJ, trivial⟩
  case n9 =>
    pnode Print.b9 Print.b9_ok n9; rw [N, PrintA.N, Print.b9_run]
    obtain ⟨⟨k, hL, hr⟩, hs⟩ := hJ
    simp only [hs, subs_z]
    by_cases hz : σ.slot (-32) = C11
    · simp only [hz, decide_true, ite_true]
      hit PN.loop
      refine ⟨k, hL, ?_⟩
      rcases hr with ⟨-, hP⟩ | ⟨h0, hle, -⟩ | ⟨hw, -⟩
      · exact hP
      · rw [hz] at hle; have := hL.2.2.2.2; simp only [C11, BitVec.toNat_ofNat] at hle; omega
      · exact absurd hz (refused_ne11 hw)
    · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
      hit PN.n10
      refine ⟨k, hL, ?_⟩
      rcases hr with ⟨h11, -⟩ | h
      · exact absurd h11 hz
      · exact h
  case n10 => pnode Print.b10 Print.b10_ok n10; rw [N, PrintA.N, Print.b10_run]; hit PN.chk3; exact hJ
  case chk3 =>
    pnode Print.b11 Print.b11_ok chk3; rw [N, PrintA.N, Print.b11_run]
    obtain ⟨k, hL, hr⟩ := hJ
    rcases hr with ⟨h0, hle, hP⟩ | ⟨hw, hQ⟩
    · have hn : ¬ ((StatusFlags.subs (σ.slot (-32)) (σ.slot (-32)) 0#64).z = true ∨
          ¬(StatusFlags.subs (σ.slot (-32)) (σ.slot (-32)) 0#64).n =
            (StatusFlags.subs (σ.slot (-32)) (σ.slot (-32)) 0#64).v) := by
        rw [subs0_le]; exact pos_not_le h0 (by omega)
      simp only [hn, ite_false]
      hit PN.n12
      exact ⟨k, hL, h0, hle, hP⟩
    · have hy : ((StatusFlags.subs (σ.slot (-32)) (σ.slot (-32)) 0#64).z = true ∨
          ¬(StatusFlags.subs (σ.slot (-32)) (σ.slot (-32)) 0#64).n =
            (StatusFlags.subs (σ.slot (-32)) (σ.slot (-32)) 0#64).v) := by
        rw [subs0_le]; exact refused_le hw
      simp only [hy, ite_true]
      hit PN.fail
      exact ⟨k, hQ⟩
  case n12 => pnode Print.b12 Print.b12_ok n12; rw [N, PrintA.N, Print.b12_run]; hit PN.adv; exact hJ
  case adv =>
    pnode Print.b13 Print.b13_ok adv; rw [N, PrintA.N, Print.b13_run]; hit PN.loop
    obtain ⟨k, ⟨h16, h8, h48, h40, hk⟩, h0, hle, hP⟩ := hJ
    refine ⟨k + (σ.slot (-32)).toNat, ⟨?_, ?_, ?_, ?_, by omega⟩, hP⟩
    · simp [Spike.Lib.upd_apply, h16]
    · simp [Spike.Lib.upd_apply, h8]
    · simp only [Spike.Lib.upd_apply]; simp only [show (-48 : Int) ≠ -40 by decide, ite_true, ite_false]
      rw [h48, adv_buf]
    · simp only [Spike.Lib.upd_apply, ite_true]; rw [h40, adv_len hl64 hle]
  case fail =>
    pnode Print.b14 Print.b14_ok fail; rw [N, PrintA.N, Print.b14_run]; exit Print.PX.abort
    exact ⟨by trivial, hJ⟩
  case done =>
    pnode Print.b16 Print.b16_ok done; rw [N, PrintA.N, Print.b16_run]; exit Print.PX.ret
    · rw [hJ.2.1]
    · exact ⟨hJ.1, hJ.2.1, hJ.2.2⟩

/-- **`hsvc_of_emitT` off the transfer sites**: the `write` system call's
node inside `NNZP SysW1` (`x0 = 1`, `x8 = 64` decode to a `write` to fd 1;
`nodeW_nnzPSvc`), `Z` at it (`hZ`). -/
theorem hsvc_of_emitTNN (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F)
    (hlen : ∀ k c, P k c → len0 < 2 ^ 63)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc).pc [svcDir])
    (hPQ : ∀ k c, P k c → Q k c)
    (hbyte : ∀ s c, At exe endPc R F ((N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc).withTp tp) s c →
      ∀ k j c1, k + j < len0 → P (k + j) c1 → ms.bo s ((buf0 + BitVec.ofNat 64 k).toNat + j) c1 (P (k + j + 1)))
    (hwe : ∀ s c, At exe endPc R F ((N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc).withTp tp) s c →
      ∀ k c1, Q k c1 → ms.we s c1)
    (hZ : NodeW Z (fun _ _ => False) exe endPc R F
      ((N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc).withTp tp)) :
    SegTC (NNZP SysW1 exe endPc Z) p lbl ms
      (At exe endPc R F ((N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc).withTp tp))
      (At exe endPc R F ((N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .n5).withTp tp)) := by
  refine step_ndNNP (nodeW_nnzPSvcA (fun s he hn => hcode s he hn) ?_ hZ) fun s c hAt => ?_
  · rintro σ c ⟨⟨-, h0, h8, -, -⟩, -⟩ call hd
    have h8' : σ.regs.X8.toNat = 64 := by rw [h8]; rfl
    have h0' : σ.regs.X0.toNat = 1 := by rw [h0]; rfl
    simp [svcCall, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.a64, Scc.Sem.A64.xRegs, h8', h0'] at hd
    exact ⟨_, _, hd.symm⟩
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨⟨k, hL, hk, hP⟩, h0, h8, h1, h2⟩, htp⟩ := id hAt
  obtain ⟨h16, h8', h48, h40, hkl⟩ := hL
  have hl := hlen k c hP
  have hc : Lower.A64.CellAt s svcDir 4 :=
    (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp [ND.withTp])
  have hx1 : s.st.1.regs.X1.toNat = (buf0 + BitVec.ofNat 64 k).toNat := by
    rw [hA.regs, ← h48, ← h1]; rfl
  have hx2 : s.st.1.regs.X2.toNat = len0 - k := by
    rw [hA.regs, UInt64.toNat, h2, h40, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hd : Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
      some (.write 1 (buf0 + BitVec.ofNat 64 k).toNat (len0 - k)) := by
    have hr0 : s.st.1.regs.X0 = 1 := by rw [hA.regs]; exact h0
    have hr8 : s.st.1.regs.X8 = 64 := by rw [hA.regs]; exact h8
    simp [Scc.Sem.A64.abi, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.a64, Scc.Sem.A64.xRegs, hr0, hr8, ← hx1,
      ← hx2]
  refine Out.toT (.emit Scc.Sem.A64.abi _ _ (fun j c1 => P (k + j) c1) (Q k) hK (Scc.Sem.A64.atSvc_of_cellAt hc) hd
    ⟨c, .refl c, hP⟩ (fun j hj c1 h => hbyte s c hAt k j c1 (by omega) h)
    (fun j hj c1 hPj r _ hr => ⟨?_, fun hj0 _ => ?_⟩) (fun c1 h => hwe s c hAt k c1 h))
  · rw [Scc.Sem.A64.abi_ret_of_cellAt hc r]
    have hA' : Flow.Abs R oI { s.st.1 with regs := { s.st.1.regs with X0 := UInt64.ofNat r.toNat } }
        (svcStep r σ) := by
      refine Flow.Abs.weaken (o' := oI) (o := oI.kill .X0) (by decide)
        ⟨by simp only [svcStep, hA.regs], hA.status, ?_, hA.slot⟩
      refine hA.so.kill .X0 fun r hr => ?_
      rcases r with y | _
      · cases y <;> first | rfl | exact absurd rfl hr
      · rfl
    have hD' : F { s.st.1 with regs := { s.st.1.regs with X0 := UInt64.ofNat r.toNat } } :=
      hF _ _ hD fun _ _ _ => rfl
    refine ⟨he, hn, hdc, ?_, svcStep r σ, hA', hD', ⟨k, ⟨h16, h8', h48, h40, hkl⟩, ?_⟩, htp⟩
    · simp only [svcRet, after, hpc]; rfl
    · have hx0 : (svcStep r σ).regs.X0.toBitVec = r := by simp [svcStep]
      rw [hx0]
      exact rc0_of_retOk (hlen _ _ hPj) hj (hPQ k c1) hPj hr
  · subst hj0; exact hPQ k c1 hPj
/-- **print inside hello's fragment**: `seg_printFANN` at `SysW1` with
`hsvc_of_emitTNN`, then `NNZP.toH`. -/
theorem seg_printFAH (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hlen : len0 < 2 ^ 63)
    (hcode : PrintF.Code c0 x29 ra exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L9_scc_rt_print.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 4 + 4 + 4 + 4 + 4 + 4)
    (hPQ : ∀ k c, P k c → Q k c)
    (hbyte : ∀ s c, At exe endPc R F ((N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc).withTp tp) s c →
      ∀ k j c1, k + j < len0 → P (k + j) c1 → ms.bo s ((buf0 + BitVec.ofNat 64 k).toNat + j) c1 (P (k + j + 1)))
    (hwe : ∀ s c, At exe endPc R F ((N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc).withTp tp) s c →
      ∀ k c1, Q k c1 → ms.we s c1)
    (hZ : ∀ i, NodeZA Z exe endPc R F ((N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q i).withTp tp)
      (blkN i)) :
    SegTC (NNZH exe endPc Z) p lbl ms
      (At exe endPc R F ((N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .e).withTp tp))
      (fun s c => ∃ x, At exe endPc R F
        ((PrintA.E (_root_.Executable.labels exe).label x29 ra len0 P Q x).withTp tp) s c) :=
  (seg_printFANN hF hR hal hlo hhi hlen hcode hentry
    (hsvc_of_emitTNN hK hF (fun _ _ _ => hlen) (fun s he hn => hcode.svc s he hn) hPQ hbyte hwe (hZ .svc).toW)
    hZ).mono_S fun _ _ h => h.toH

end ProofNN

end FA

/-! ## The call -/

section CallNN

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _}
  {N' : ι → ND} {E' : κ → ND} {Sy : Scc.Sem.Kernel.Call → Prop} {Z : Frag isaLSE2}

/-- **`printF_callT` off the transfer sites** (`call_ndTS` with
`seg_printFANN`): the write system call (`hsvc`) inside `NNZP Sy`, `Z` at
the callee's nodes at every realizable call state (`hZ`). -/
theorem printF_callTNN {nC : ND} {Pc Qc : AS → Nat → Ctl → Prop}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hF : FStable R F)
    (hlo : R.lo ≤ nC.o.sp + -48) (hhi : nC.o.sp < R.hi) (hk16 : nC.o.sp % 16 = 0)
    {c0' : Ctl} {x29' ra' : BitVec 64} (hcode : PrintF.Code c0' x29' ra' exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L9_scc_rt_print.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 4 + 4 + 4 + 4 + 4 + 4)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    (hP0 : ∀ σ c, nC.J σ c → Pc σ 0 c)
    (hlen : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat < 2 ^ 63)
    (hsvc : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -48 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ σC c, nC.J σC c →
      SegTC (NNZP Sy exe endPc Z) p lbl ms (At exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc σC .svc))
        (At exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc σC .n5)))
    (hZ : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -48 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ σC c, nC.J σC c →
      ∀ i, NodeZA Z exe endPc R' F' (cN (_root_.Executable.labels exe).label Pc Qc σC i) (FA.blkN i))
    (hret : ∀ σC c σR c', nC.J σC c →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      σR.regs.TPIDR_EL0 = σC.regs.TPIDR_EL0 → Pc σC σC.regs.X1.toBitVec.toNat c' →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp (-48) 0).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N' E' ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨nC.o.sp, []⟩, σR⟩ c')
    (habort : ∀ σC c σR c' k, nC.J σC c → σR.regs.X0 = 4 → Qc σC k c' →
      (∀ k, R.Off k → ¬ (R.callee nC.o.sp (-48) 0).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N' E' ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨nC.o.sp + -48, []⟩, σR⟩ c') :
    SegTC (NNZP Sy exe endPc Z) p lbl ms (At exe endPc R F nC) (Next exe endPc R F N' E') := by
  refine call_ndTS (lo' := -48) (hi' := 0) (Ne := cNe (_root_.Executable.labels exe).label Pc Qc nC)
    (Ex := fun σC x => (PrintA.E (_root_.Executable.labels exe).label σC.regs.X29.toBitVec σC.regs.X30.toBitVec
      σC.regs.X1.toBitVec.toNat (Pc σC) (Qc σC) x).withTp σC.regs.TPIDR_EL0)
    hR hal hF hlo (by decide) hhi (by decide) hk16 (by decide) (by decide)
    (fun R' F' hR' hal' hlo' hhi' hF' hFF σC => ?_) (fun _ => rfl) ?_ ?_
  · by_cases hg : ∃ c0, nC.J σC c0
    · obtain ⟨c0, hJ0⟩ := hg
      refine (FA.seg_printFANN hF' hR' hal' hlo' hhi' (hlen σC c0 hJ0) (c0 := c0) (tp := σC.regs.TPIDR_EL0)
        hcode.ghost hentry
        (hsvc R' F' hR' hal' hlo' hhi' hF' hFF σC c0 hJ0) (hZ R' F' hR' hal' hlo' hhi' hF' hFF σC c0 hJ0)).mono_pre ?_
      rintro s c ⟨a, b, d, e, σ, hA, hD, hJ', -, -⟩
      exact ⟨a, b, d, e, σ, hA, hD, hJ'⟩
    · exact SegTC.step (fun s c ⟨_, _, _, _, _, _, _, _, _, h⟩ => absurd h hg)
        fun s c ⟨_, _, _, _, _, _, _, _, _, h⟩ => absurd h hg
  · intro σC c hJ
    exact ⟨σC, by rw [hpc]; rfl, ⟨⟨hP0 σC c hJ, rfl, rfl, rfl, by simp [enter]⟩, rfl⟩, rfl, c, hJ⟩
  · rintro g y σC c σx c' σR hJ ⟨-, he, -⟩ hx hreg - hsl
    obtain rfl : σC = g := enter_inj he
    cases y
    · obtain ⟨⟨h29, h30, hP⟩, htp⟩ := hx
      have h := hret σC c σR c' hJ (by rw [hreg]; exact h29) (by rw [hreg]; exact h30) (by rw [hreg]; exact htp) hP
        hsl
      simpa [PrintA.E, Print.oE, ND.withTp] using h
    · obtain ⟨⟨h4, k, hQ⟩, -⟩ := hx
      exact habort σC c σR c' k hJ (by rw [hreg]; exact h4) hQ hsl

end CallNN

end Spike.Lib.A64.Flow.Worker.PrintF
