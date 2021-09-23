never  {    /* <>(q) */
T0_init:
        do
        :: atomic { ((q)) -> assert(!((q))) }
        :: (1) -> goto T0_init
        od;
accept_all:
        skip
}
