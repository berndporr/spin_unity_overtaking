bool crashed = false, overtook = false;
#define q (overtook == true)
# include "nc_overtake.pml"
mtype = {left, right, far_behind, close_behind, same, close_ahead, far_ahead}
mtype position = far_behind, lane = left;
inline choose_action()
{
    do
    :: goto drive;
    :: goto brake;
    :: goto advance;
    :: goto left_lane_change;
    :: goto right_lane_change;
    od;
}

proctype main()
{
    goto drive;
    advance:
        printf("STATE_accelerate\n");
    /* Move forwards */
            if
            :: atomic{position == far_behind -> position = close_behind};
            :: atomic{position == close_behind -> position = same};
            :: atomic{position == same -> position = close_ahead};
            :: atomic{position == close_ahead -> position = far_ahead};
            fi;
            goto drive;
    left_lane_change:
        printf("STATE_left_lane_change\n");
        lane = left;
        goto drive;
    right_lane_change:
        printf("STATE_right_lane_change\n");
        lane = right;
        goto drive;
    brake:
        printf("STATE_brake\n");
    /* Advance backwards */
            if
            :: atomic{position == far_ahead -> position = close_ahead};
            :: atomic{position == close_ahead -> position = same};
            :: atomic{position == same -> position = close_behind};
            :: atomic{position == close_behind -> position = far_behind};
            fi;
            goto drive;
    drive:
        printf("STATE_drive\n");
        /* Check if we have crashed or completed the overtake. If not, choose a new random action to do */
        if
        :: (position == same && lane == left) -> crashed = true;
        :: (position == far_ahead && lane == left && crashed == false) -> overtook = true;
        :: else -> choose_action();
        fi;
}

init {
    atomic{
        run main();
    };
}
