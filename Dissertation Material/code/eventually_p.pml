never  {    /* <>p */
T0_init:
	do
	:: atomic { ((p)) -> assert(!((p))) }
	:: (1) -> goto T0_init
	od;
accept_all:
	skip
}
