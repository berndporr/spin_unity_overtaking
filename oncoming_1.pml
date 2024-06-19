bool crashed = false, overtook = false;
#define q (overtook == true)
#include "nc_overtake.pml"
mtype = {left, right}
mtype lane = left;
byte pos_autonomous = 0, pos_oncoming = 10, pos_other = 3; /* Declare initial starting positions */
byte overtaking_pos = 4; /* what position should autonomous car reach so we could say that it successfully overtook the other car*/
byte road_length = 10;
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

inline update_oncoming()
{
    /* Update oncoming car */
    if
    :: atomic{pos_oncoming > 0 -> pos_oncoming--;}
    :: else -> skip;
    fi;
}

inline check_crash()
{
    if
    :: (pos_autonomous == pos_other && lane == left) -> crashed = true; printf("Crashed to other\n"); goto finish;
    :: (pos_autonomous == pos_oncoming && lane == right) -> crashed = true; printf("Crashed to oncoming\n"); goto finish;
    :: else -> skip;
    fi;
}

proctype main()
{
    goto drive;
    advance:
    /* Move forwards */
        printf("advance\n");
        if
        :: atomic{pos_autonomous < road_length -> pos_autonomous++;};
        :: else -> skip;
        fi;
        goto drive;
    left_lane_change:
        printf("left_lane_change\n");
        lane = left;
        goto drive;
    right_lane_change:
        printf("right_lane_change\n");
        lane = right;
        goto drive;
    brake:
        printf("brake\n");
        /* Advance backwards */
        if
        :: atomic{pos_autonomous > 0 -> pos_autonomous--;};
        :: else -> skip;
        fi;
        goto drive;
    drive:
        printf("\ndrive:\npos_autonomous:%u\npos_oncoming:%u\n\n", pos_autonomous, pos_oncoming);
        atomic{check_crash(); update_oncoming(); check_crash()};
        /* Check if autonomous car completed the overtake. If not, choose a new random action to do */
        if
        :: (pos_autonomous > overtaking_pos && lane == left) -> overtook = true; goto finish;
        :: else -> choose_action();
        fi;
    finish:
}
init {
    atomic{
        run main();
    };
}
