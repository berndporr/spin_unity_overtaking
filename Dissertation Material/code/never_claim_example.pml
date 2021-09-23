bool overtook = false;
#define p (overtook == true)
#include "eventually_p.pml" /* Includes the Never Claim generated from <>p */

proctype main() {
    ....
    if
    :: (overtook == false) -> overtook = true;
    :: else -> skip;
    fi
    ....
}
init {
    atomic{
        run main();
    }
}
