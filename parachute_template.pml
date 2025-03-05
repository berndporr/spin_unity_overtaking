bool crashed = false, prepared = false;
#define q (prepared == true)
#include "nc_overtake.pml"
mtype = {left, right}
mtype lane = PLACEHOLDER_LANE;
mtype starting_lane = lane;
int pos_oncoming = PLACEHOLDER_ONCOMING_POSITION, pos_other = PLACEHOLDER_OTHER_POSITION, pos_next_oncoming = PLACEHOLDER_NEXT_ONCOMING_POSITION, pos_rear = PLACEHOLDER_REAR_POSITION; /* Declare initial starting positions */
byte num_obstacles = PLACEHOLDER_NUM_OBSTACLES;
byte obstacles[num_obstacles] = {PLACEHOLDER_OBSTACLES};
byte road_length = 50;
byte oncoming_end_pos = 0;
byte numLaneChanges = 0, numAllowedLaneChanges = 1;
byte num_done_actions = 0, max_actions = 100;

byte i;

inline choose_action()
{
    /* Choose one of the five possible actions */
    num_done_actions++;
    do
    :: (lane != left && numLaneChanges < numAllowedLaneChanges) -> goto left_lane_change;
    :: goto accelerate;
    :: (lane != right && numLaneChanges < numAllowedLaneChanges) -> goto right_lane_change;
    :: goto drive;
    :: goto brake;
    od;
}

inline update_oncoming()
{
    check_crash();
    /* Update oncoming car */
    if
    :: (pos_oncoming > 0) -> pos_oncoming--;
    :: else -> skip;
    fi;

    if
    :: (pos_next_oncoming > oncoming_end_pos) -> pos_next_oncoming--;
    :: else -> skip;
    fi;
    check_crash();
}

inline check_crash()
{
    if
    :: (pos_other == 10 && lane == left) -> crashed = true; printf("Crashed to other\n"); goto finish;
    :: (pos_oncoming == 10 && lane == right) -> crashed = true; printf("Crashed to oncoming\n"); goto finish;
    :: (pos_next_oncoming == 10 && lane == right) -> crashed = true; printf("Crashed to next oncoming\n"); goto finish;
    :: (pos_rear == 10 && lane == left) -> crashed = true; printf("Crashed to rear\n"); goto finish;
    :: (num_done_actions >= max_actions) -> crashed = true; printf("too many actions\n"); goto finish; /* It is technically not a crash, but this way LTL is simplier*/
    :: else -> skip;
    fi;

    for (i : 0 .. num_obstacles -1){
        if
        :: (obstacles[i] == 10 && lane == left) -> crashed = true; printf("Crashed to obstacle\n"); goto finish;
        :: else -> skip;
        fi;
    }
}

proctype mainProc()
{
    goto main;
    accelerate:
    /* Move forwards */
        printf("STATE_accelerate\n");

        for (i : 0 .. num_obstacles - 1) {
            if
            :: (obstacles[i] > 0) -> obstacles[i]--; /* Keep AV stationary and bring other car closer */
            :: else -> skip;
            fi;
        }
        if
        :: (pos_other > 0) -> pos_other--; /* Keep AV stationary and bring other car closer */
        :: else -> skip;
        fi;

        if
        :: (pos_rear > 0) -> pos_rear--; /* Keep AV stationary and bring other car closer */
        :: else -> skip;
        fi;

        update_oncoming(); /* Keep AV stationary and bring oncoming car closer */
        update_oncoming(); /* Let AV drive on its own as in other states */
        goto main;
    left_lane_change:
        printf("STATE_left_lane_change\n");
        lane = left;
        update_oncoming();
        numLaneChanges++;
        goto main;
    right_lane_change:
        printf("STATE_right_lane_change\n");
        lane = right;
        update_oncoming();
        numLaneChanges++;
        goto main;
    brake:
        /* Since non-existent cars are positioned at 0, braking would bring them forwards, but if we put AI car far enough, this should not cause any problems*/
        printf("STATE_brake\n");
        /* Advance backwards */
        if
        :: (pos_other < road_length) -> pos_other++;
        :: else -> skip;
        fi;

        if
        :: (pos_rear < road_length) -> pos_rear++;
        :: else -> skip;
        fi;

        for (i : 0 .. num_obstacles - 1){
            if
            :: (obstacles[i] < road_length) -> obstacles[i]++; /* Keep AV stationary and bring other car closer */
            :: else -> skip;
            fi;
        }

        update_oncoming();
        update_oncoming();
        goto main;
    drive:
        printf("STATE_drive\n");
        update_oncoming();
        goto main;
    main:
        printf("\nmain:\npos_oncoming:%u\npos_other:%u\npos_next_oncoming:%u\npos_rear:%u\nnum_actions:%u\n\n", pos_oncoming, pos_other, pos_next_oncoming, pos_rear, num_done_actions);
        update_oncoming();

        /* Check if AV completed the overtake. If not, choose a new random action to do */
        if
        :: (starting_lane == left && pos_other == 11 && pos_next_oncoming <= 10) -> prepared = true; goto finish;
        :: (starting_lane == right && lane == left  && pos_next_oncoming <= 10) -> prepared = true; goto finish;
        :: else -> choose_action();
        fi;

    finish:
        printf("\nfinish:\npos_oncoming:%u\npos_next_oncoming:%u\npos_other:%u\npos_rear:%u\nlane:%u\n\n", pos_oncoming, pos_next_oncoming, pos_other, pos_rear, lane);
}
init {
    atomic{
        run mainProc();
    };
}
