import L6Poly.Basic
import L6Check.Certs.C12751a0d4df69421

/-! Cofactor certificates, batch 0: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_12751a0d4df69421 : L6.Poly.checkCert L6.Certs.C12751a0d4df69421 = true := by native_decide

end L6.Poly.Checks
