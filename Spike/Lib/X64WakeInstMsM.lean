/-
**main's memory side `msM` is satisfiable at its post-spawn runtime
accesses** (x86-64 only; no AArch64 twin): `X64WakeInst.msM hp i T W g =
msXW (wakeMs hp i g) T T W` narrows main's runtime writes to words off both
self words `⟨T, 8⟩`, `⟨W, 8⟩`. `msM` is only used after the spawn
(`X64WakeInst.wakeM`'s `Mi`, built by `X64WakeInstR.main_closed_wakeWR`),
where main's runtime accesses are the park's thread-pointer load `%fs:0 = T`
(`LdOk`), the prologue's limit load `%fs:8 = T + 8` (`LimOk`) and the park's
exchange at `T + 16` (`StOk`, the only runtime write). Main's write of the
second TCB's self word `⟨W, 8⟩` (the second `scc_rt_thread_init`'s store at
`tcb2 + 0`) is before the clone, at the pre-spawn instances (`ownG`, not
`msM`), so `msM`'s narrowing never meets it.

- `ldOk_msM`, `limOk_msM`: the loads' facts transfer from `wakeMs` (a read's
  `mp … false` is unchanged by the narrowing).
- `stOk_msM_park`: the park's exchange at `T + 16` transfers from `wakeMs`,
  given `T + 24` in the address space and the word `⟨T + 16, 8⟩` off `W`'s
  (the two TCBs' words apart; discharged at the instance from the TCB
  placement, with `X64-SelfOK`).
-/
import Spike.Lib.X64WakeInst

namespace Spike.Lib.X64WakeInst

open Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Flow.Ret0 (LimOk StOk LdOk)
open Spike.Lib.X64WakeOwnX (OffTcb msXW_mp_of offTcb_add)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat) {T W : BitVec 64} {g : Gh}
  {F : MachineData → Prop}

/-- The park's thread-pointer load at `msM`. -/
theorem ldOk_msM {a : BitVec 64} (h : LdOk (wakeMs hp i g) F a) : LdOk (msM hp i T W g) F a :=
  ⟨h.rt, ⟨h.mp, fun h => nomatch h⟩, h.unmapped⟩

/-- The prologue's limit load at `msM`. -/
theorem limOk_msM {a Z : BitVec 64} (h : LimOk (wakeMs hp i g) F a Z) : LimOk (msM hp i T W g) F a Z :=
  ⟨h.rt, ⟨h.mp, fun h => nomatch h⟩, h.unmapped, h.room⟩

/-- **The park's exchange at `T + 16` at `msM`**: off `T`'s word (no
wrap-around, `hT`) and off `W`'s (`hW`). -/
theorem stOk_msM_park (h : StOk (wakeMs hp i g) F (T + 16#64) 0#64) (hT : T.toNat + 24 ≤ 2 ^ 64)
    (hW : OffTcb W ⟨T + 16#64, 8⟩) : StOk (msM hp i T W g) F (T + 16#64) 0#64 :=
  ⟨h.rt, msXW_mp_of h.mp (offTcb_add (k := 16) (by decide) (by omega)) hW, h.G, h.unmapped⟩

end Spike.Lib.X64WakeInst

/-- info: 'Spike.Lib.X64WakeInst.stOk_msM_park' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.stOk_msM_park
