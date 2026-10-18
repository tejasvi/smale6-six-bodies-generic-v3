import L6Poly.Basic
import L6Check.Certs.Ce5214ed98eccc982

/-! Cofactor certificates, batch 45: `checkCert` of each embedded text (`native_decide`). -/

namespace L6.Poly.Checks

set_option maxHeartbeats 0 in
theorem cert_e5214ed98eccc982 : L6.Poly.checkCert L6.Certs.Ce5214ed98eccc982 = true := by native_decide

end L6.Poly.Checks
