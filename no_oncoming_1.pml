/*Integers explained:
  dist_*:
  1: close (needs actions)
  2: medium (just right)
  3: far (no obstacles)

  speed:
  1: slow
  2: medium
  3: fast
*/

proctype main()
{
  byte speed = 2;
  byte dist_right = 3;
  byte dist_left = 2;
  byte dist_front = 1;
  byte legal_speed = 3;
  byte normal_speed = 2;

  going_straight:
    if
    :: dist_front == 1; goto going_right;
    fi;
  going_right:
    dist_right--; // obstacles from the right get closer
    dist_left++; // going further from the left
    if
    :: dist_right > 1 && dist_left > 1 -> dist_front = 3; goto going_straight_acc; // Since this model doesn't have oncoming cars we are in an empty lane. we will not crash to obstacles on both sides
    :: dist_right == 1 -> goto going_left;
    :: dist_left == 1 -> goto going_right;
    fi;
  going_left:
    dist_left--;
    dist_right++;
    if
    :: dist_right > 1 && dist_left > 1 -> dist_front = 3; goto going_straight_dec; // Since this model doesn't have oncoming cars we are in an empty lane. we will not crash to obstacles on both sides
    :: dist_right == 1 -> goto going_left;
    :: dist_left == 1 -> goto going_right;
    fi;
  going_straight_acc:
    speed++;
    if
    :: dist_left > 1; goto going_left;
    :: speed < legal_speed -> goto going_straight_acc;
    :: speed == legal_speed -> goto going_straight_maintaining_speed;
    fi;
  going_straight_maintaining_speed:
    if
    ::dist_left > 1; goto going_left;
    fi;
  going_straight_dec:
    speed--;
    if
    :: speed > normal_speed -> goto going_straight_dec;
    :: speed == normal_speed -> goto going_straight;
    fi;
}

init {
  run main()
}
