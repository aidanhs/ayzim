// Emopt doesn't optimise this, but it (and ayzim) probably could with some work -
// it just means keeping track of where to insert a stat outside of the label
function xyz() {
 var $0 = 0;
 $0 = 0 | 0;
 L19 : while (1) {
  $0 = $0 + 1 | 0;
  if ($0 >>> 0 >= 3) {
   somefn() | 0;
   break;
  }
 }
 return;
}
// Meanwhile, emopt does optimise this but ayzim doesn't. Fixing this in ayzim
// would likely fix the above, but it's not a particularly exciting optimisation
function xyz() {
 var $0 = 0;
 $0 = 0 | 0;
 L19 : while (1) {
  $0 = $0 + 1 | 0;
  if ($0 >>> 0 >= 3) {
   break;
  }
 }
 return;
}

