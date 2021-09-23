using System.Collections;
using System.Collections.Generic;
using UnityEngine;

public struct Environment
{
    private int distFront, distBack, distLeft, distRight, distOncoming, distNext;
    private bool obsFront, obsRear, obsLeft, obsRight, obsOncoming, obsNext;
    private float x_coord;
    private int roadSegmLength, aiCarPosition;
    private List<int> obstaclesPositions;
    private List<string> obstaclesNames;

    public void init() {
        this.distFront = -1;
        this.distBack = -1;
        this.distLeft = -1;
        this.distRight = -1;
        this.distOncoming = -1;
        this.distNext = -1;
        this.x_coord = 0; // This is used to decide on which lane an autonomous car is
        this.roadSegmLength = 21;
        this.aiCarPosition = 10;
        this.obsFront = false;
        this.obsRear = false;
        this.obsRight = false;
        this.obsLeft = false;
        this.obsOncoming = false;
        this.obsNext = false;
        this.obstaclesPositions = new List<int>();
        this.obstaclesNames = new List<string>();
    }

    public void SetObstaclesPositions(List<float> obstacles) {
        obstacles.Sort();
        float closestFront = -1, closestRear = -1;
        obstaclesPositions = new List<int>();
        foreach (float dist in obstacles) {
            if (dist > 0)
            {
                obstaclesPositions.Add(LongitudinalDistToRoadSegm(dist + roadSegmLength / 2) + aiCarPosition); // detected car is in front

                if (closestFront == -1 || dist < closestFront)
                    closestFront = dist;
            }
            else {
                obstaclesPositions.Add(LongitudinalDistToRoadSegm(dist + 0.5f - roadSegmLength / 2) + aiCarPosition); // detected car is at the back.  Add one to fix the Ceil converting to the wrong side in LongitudinalDistToRoadSegm
                if (closestRear == -1 || -dist < closestRear)
                    closestRear = -(dist + 0.5f);
            }
        }
        SetDistBack(closestRear);
        SetDistFront(closestFront);
    }

    public void SetObstaclesNames(List<string> names)
    {
        obstaclesNames = names;
        obstaclesNames.Sort();
    }

    public void SetDistFront(float dist) {
        if (dist != -1)
        {
            distFront = (int)dist  + roadSegmLength / 2; //  compensate for road segment size
            obsFront = true;
        }
        else {
            distFront = -1;
            obsFront = false;
        }
    }

    public void SetDistBack(float dist) {
        if (dist != -1)
        {
            distBack = (int)dist + roadSegmLength / 2; // compensate for road segment size
            obsRear = true;
        }
        else {
            distBack = -1;
            obsRear = false;
        }
    }

    public void SetDistRight(float dist) {
        if (dist != -1)
        {
            distRight = (int)dist;
            obsRight = true;
        }
        else {
            distRight = -1;
            obsRight = false;
        }

    }

    public void SetDistLeft(float dist) {
        if (dist != -1)
        {
            distLeft = (int)dist;
            obsLeft = true;
        }
        else {
            distLeft = -1;
            obsLeft = false;
        } }

    public void SetX(float x) {
        x_coord = x;
    }
    public void SetDistOncoming(float dist)
    {
        if (dist != -1)
        {
            distOncoming = (int)dist + roadSegmLength / 2; // compensate for road segment size
            obsOncoming = true;
        }
        else
        {
            distOncoming = -1;
            obsOncoming = false;
        }
    }

    public void SetDistNext(float dist) {
        if (dist != -1)
        {
            distNext = (int)dist + roadSegmLength / 2; // compensate for road segment size
            obsNext = true;
        }
        else {
            distNext = -1;
            obsNext = false;
        }
    }

    // There are 2 lanes
    public int getLane() {
        if (x_coord >= -2 && x_coord <= 3.5f)
        {
            return 0;
        }
        else if (x_coord > 3.5f && x_coord <= 6)
        {
            return 1;
        }
        else return 2; // Lane 2 indicates lane error
    }

    public int GetDistOncoming() {
        return LongitudinalDistToRoadSegm(distOncoming);
    }

    public int GetDistNext() {
        return LongitudinalDistToRoadSegm(distNext);
    }

    public int GetDistRight() {
        if (distRight > 0)
        {
            return 1;
        }
        else
        {
            return 0;
        }
    }

    public int GetDistLeft()
    {
        if (distLeft > 0)
        {
            return 1;
        }
        else
        {
            return 0;
        }
    }

    // convert physical distance to objects to more abstract positions on the road (road is divided to 10 sections)
    public int GetDistFront() {

        return LongitudinalDistToRoadSegm(distFront);
    }

    // convert physical distance to objects to more abstract positions on the road (road is divided to 10 sections)
    public int GetDistBack()
    {

        return LongitudinalDistToRoadSegm(distBack);
    }

    private int LongitudinalDistToRoadSegm(float var) {
        return (int)(Mathf.Ceil(var)) / roadSegmLength;
}


    public int GetOtherPosition()
    {

        if (isObsLeft())
            return aiCarPosition;
        else if (isObsFront())
            return GetDistFront() + aiCarPosition; // Add one since in oncoming_2 autonomous car starts in position 1
        else return 0;
    }

    public int GetNextPosition() {
        if (isObsLeft() && isObsFront())
        {
            return GetDistFront() + aiCarPosition; // if we are sensing a car to the side of us, than what we sense with front sensor must be the next car.
        }
        else if (isObsFront() && isObsNext() && GetDistFront() != GetDistNext()) {
            return GetDistNext() + aiCarPosition;
        }
        else {
            return 0; // if there is no car parallel to use, then what we sense in front is other car and we don't know if next car exists.
        }
    }

    public int GetOncomingPosition()
    {

        if (isObsRight())
            return aiCarPosition;
        else
            return 0;
    }

    // By default we are always sensing the next oncoming. this is because of model checker logic.
    public int GetNextOncomingPosition() {
        if (isObsOncoming())
            return GetDistOncoming() + aiCarPosition;
        else
            return 0;
    }

    public int GetRearPosition() {
        if (isObsBack())
        {
            return aiCarPosition - GetDistBack();
        }
        else {
            return 0;
        }
    }

    public List<int> GetObstaclesPositions() {
        return obstaclesPositions;
    }

    public List<string> GetObstaclesNames() {
        return obstaclesNames;
    }

    public bool isObsFront() {
        return obsFront;
    }

    public bool isObsBack() {
        return obsRear;
    }

    public bool isObsOncoming() {
        return obsOncoming;
    }

    public bool isObsRight() {
        return obsRight;
    }

    public bool isObsLeft() {
        return obsLeft;
    }

    public bool isObsNext() {
        return obsNext;
    }

    public int GetAiCarPosition() {
        return aiCarPosition;
    }

    public override string ToString() =>
        $"otherPos: {GetOtherPosition()}\nrearPos: {GetRearPosition()}\nfrontPos: {GetNextPosition()}\noncomingPos:{GetOncomingPosition()}\nnextOncomingPos: {GetNextOncomingPosition()}\n\nfrontDist: {GetDistFront()}\nrearDist: {GetDistBack()}";
}
