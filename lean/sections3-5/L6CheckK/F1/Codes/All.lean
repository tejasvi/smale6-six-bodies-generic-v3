import L6CheckK.F1.All
import L6CheckK.F1.Codes.C0
import L6CheckK.F1.Codes.C1
import L6CheckK.F1.Codes.C2
import L6CheckK.F1.Codes.C3
import L6CheckK.F1.Codes.C4
import L6CheckK.F1.Codes.C5
import L6CheckK.F1.Codes.C6
import L6CheckK.F1.Codes.C7
import L6CheckK.F1.Codes.C8
import L6CheckK.F1.Codes.C9
import L6CheckK.F1.Codes.C10
import L6CheckK.F1.Codes.C11
import L6CheckK.F1.Codes.C12
import L6CheckK.F1.Codes.C13
import L6CheckK.F1.Codes.C14
import L6CheckK.F1.Codes.C15
import L6CheckK.F1.Codes.C16
import L6CheckK.F1.Codes.C17
import L6CheckK.F1.Codes.C18
import L6CheckK.F1.Codes.C19
import L6CheckK.F1.Codes.C20
import L6CheckK.F1.Codes.C21
import L6CheckK.F1.Codes.C22
import L6CheckK.F1.Codes.C23
import L6CheckK.F1.Codes.C24
import L6CheckK.F1.Codes.C25
import L6CheckK.F1.Codes.C26
import L6CheckK.F1.Codes.C27
import L6CheckK.F1.Codes.C28
import L6CheckK.F1.Codes.C29
import L6CheckK.F1.Codes.C30
import L6CheckK.F1.Codes.C31

/-! The comparison of codes on all intervals. -/

namespace L6CheckK.F1

open L6F1 L6K.F1

theorem g_ivls : ivls.all (fun lh => ivlCheck codesAll repCodes.flatten lh.1 lh.2) = true := by
  simp only [ivls, List.all_cons, List.all_nil, Bool.and_true, L6CheckK.F1.Codes.C0.ok, L6CheckK.F1.Codes.C1.ok, L6CheckK.F1.Codes.C2.ok, L6CheckK.F1.Codes.C3.ok, L6CheckK.F1.Codes.C4.ok, L6CheckK.F1.Codes.C5.ok, L6CheckK.F1.Codes.C6.ok, L6CheckK.F1.Codes.C7.ok, L6CheckK.F1.Codes.C8.ok, L6CheckK.F1.Codes.C9.ok, L6CheckK.F1.Codes.C10.ok, L6CheckK.F1.Codes.C11.ok, L6CheckK.F1.Codes.C12.ok, L6CheckK.F1.Codes.C13.ok, L6CheckK.F1.Codes.C14.ok, L6CheckK.F1.Codes.C15.ok, L6CheckK.F1.Codes.C16.ok, L6CheckK.F1.Codes.C17.ok, L6CheckK.F1.Codes.C18.ok, L6CheckK.F1.Codes.C19.ok, L6CheckK.F1.Codes.C20.ok, L6CheckK.F1.Codes.C21.ok, L6CheckK.F1.Codes.C22.ok, L6CheckK.F1.Codes.C23.ok, L6CheckK.F1.Codes.C24.ok, L6CheckK.F1.Codes.C25.ok, L6CheckK.F1.Codes.C26.ok, L6CheckK.F1.Codes.C27.ok, L6CheckK.F1.Codes.C28.ok, L6CheckK.F1.Codes.C29.ok, L6CheckK.F1.Codes.C30.ok, L6CheckK.F1.Codes.C31.ok]

end L6CheckK.F1
