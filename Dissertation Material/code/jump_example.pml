proctype main()
{
    main_loop:
        if
        :: (crashed == true) -> goto finish;
        :: else -> goto main_loop;
        fi
    finish:
        skip;
}
