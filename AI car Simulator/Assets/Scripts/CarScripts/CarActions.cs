using System;
using System.Collections;
using System.Collections.Generic;
using UnityEngine;
using UnityEngine.UI;

[RequireComponent(typeof(InputManager))]
public class CarActions : MonoBehaviour
{

    public InputManager input;
    public CarStateController carStateController;
    public GameObject turnHelper;
    public Text oldEnvText;
    public Text curEnvText;
    public Text currentAction;
    public Text collisionText;
    Environment curEnv;
    Environment oldEnv; // Environment before an action was started
    public GameObject car;
    private float turnDuration = 2.5f;
    private float maxSteerAngle = 1f;
    public float turnTimer;
    public bool turnFixRoutineStarted;
    float speedFactor;
    private float driveTime = 3f;
    private float driveTimer = 3f;

    private float maxSpeed = 7;
    private float maxDriveSpeed = 7;
    private float maxAccelerationSpeed = 14;
    private float maxBrakeSpeed = 2;
    private float startTimer = 2f;
    private int actionsDone = 0;
    private int actionsBeforeRecalc = 10;

    // Various states the car can be in
    CarStateController.CarState state;

    // Start is called before the first frame update
    void Start()
    {
        GetComponent<Rigidbody>().velocity = new Vector3(0, 0, maxSpeed);
        curEnv = GetComponent<Sensors>().env;
        oldEnv = curEnv;
    }

    // Update is called once per frame
    void Update()
    {
        if (!carStateController.gamePaused)
        {
            
            // Get obstacles
            curEnv = GetComponent<Sensors>().env;

            // Check for changes
            CheckOncomingChangeCloseToFar(curEnv, oldEnv);
            CheckObstaclesNamesChange(curEnv, oldEnv);
            //CheckNextChangeCloseToFar(curEnv, oldEnv);

            // Do actions
            switch (state)
            {
                case CarStateController.CarState.Drive:
                    if (driveTimer > 0)
                    {

                        driveTimer -= Time.deltaTime;
                        maxSpeed = maxDriveSpeed;
                    }
                    else
                    {
                        actionsDone++;
                        carStateController.doNextState = true;
                    }

                    break;
                case CarStateController.CarState.Accelerate:

                    // Go faster until distance to obstacle in front increases by one
                    if (curEnv.isObsBack() && curEnv.GetDistBack() > oldEnv.GetDistBack()) // prefer rear vehicle distance if it exists as it is more reliable
                    {
                        //print($"accelerate complete REAR CHANGE oldDistBack: {oldEnv.GetDistBack()}, newDistBack: {curEnv.GetDistBack()}");
                        maxSpeed = maxDriveSpeed;
                        carStateController.doNextState = true;
                        actionsDone++;
                    }
                    else if (!curEnv.isObsBack() && curEnv.isObsFront() && curEnv.GetDistFront() < oldEnv.GetDistFront()) // if only front sensor senses, accelerate until front change.
                    {
                        //print($"accelerate complete FRONT CHANGE, oldDistFront: {oldEnv.GetDistFront()}, newDistFront: {curEnv.GetDistFront()}");
                        maxSpeed = maxDriveSpeed;
                        carStateController.doNextState = true;
                        actionsDone++;
                    }
                    else
                    {
                        maxSpeed = maxAccelerationSpeed;
                    }



                    break;
                case CarStateController.CarState.Brake:
                    // slow down until distance to obstacle drops by one road segment
                    if (!curEnv.isObsLeft() && curEnv.isObsBack() && curEnv.GetDistBack() < oldEnv.GetDistBack()) // preffer rear vehicle distance as it is more reliable
                    {
                        //print($"brake complete FRONT CHANGE, oldDistFron: {oldEnv.GetDistFront()}, newDistFront: {curEnv.GetDistFront()}");
                        maxSpeed = maxDriveSpeed;
                        carStateController.doNextState = true;
                        actionsDone++;
                    }
                    else if (!curEnv.isObsLeft() && !curEnv.isObsBack() && curEnv.isObsFront() && curEnv.GetDistFront() > oldEnv.GetDistFront())
                    {
                        //print($"brake complete REAR CHANGE, oldDistBack: {oldEnv.GetDistBack()}, newDistBack: {curEnv.GetDistBack()}");
                        maxSpeed = maxDriveSpeed;
                        carStateController.doNextState = true;
                        actionsDone++;
                    }
                    else
                    {
                        maxSpeed = maxBrakeSpeed;
                    }
                    break;

                case CarStateController.CarState.LeftLaneChange:
                    if (curEnv.getLane() < oldEnv.getLane())
                    {
                        //carStateController.doNextState = true;
                        //print("change done");
                        carStateController.doNextState = true;
                        actionsDone++;

                    }
                    else
                    {
                        maxSpeed = maxDriveSpeed;
                    }
                    break;

                case CarStateController.CarState.RightLaneChange:
                    if (curEnv.getLane() > oldEnv.getLane())
                    {
                        carStateController.doNextState = true;
                        actionsDone++;
                        //carStateController.recalculateActions = true; // When we are on the right lane we have more information on thetraffic on the left lane, thus recalculate.
                    }
                    else
                    {
                        maxSpeed = maxDriveSpeed;
                    }
                    break;
            }

            // Check for number of actions done, recalculate if reached limit
            if (actionsDone >= actionsBeforeRecalc)
            {
                print("Recalc: number of actions before recalc reached the limit");
                actionsDone = 0;
                carStateController.recalculateActions = true;
            }


            // Maintain speed
            float currentSpeed = GetComponent<Rigidbody>().velocity.magnitude;
            if (currentSpeed < maxSpeed)
            {

                input.throttle = 1f;
                input.brake = 0f;
            }
            else if (currentSpeed - maxSpeed > 0.5)
            {
                input.throttle = 0f;
                input.brake = 3f;
            }
            else
            {
                input.throttle = 0f;
                input.brake = 0f;
            }

            //// Follow dummy cube


            float anglePos = Vector3.Angle(car.transform.position, turnHelper.transform.position);
            float angleRot = Quaternion.Angle(car.transform.rotation, turnHelper.transform.rotation);

            float x = turnHelper.transform.position.x - car.transform.position.x;
            float z = turnHelper.transform.position.z - car.transform.position.z;
            float lookAtRotation = Mathf.Atan2(x, z) * Mathf.Rad2Deg;

            float angleRotSign = x / Mathf.Abs(x);
            input.steer = (lookAtRotation - angleRot * angleRotSign);

            curEnvText.text = $"curEnv:\n{curEnv.ToString()}";
            currentAction.text = state.ToString();

            // Update oldEnv so we could compare this frame with the next
            oldEnv = curEnv; // we have to update this every frame, otherwise when sensors jump from one car to another one, old Env would be mistaking new car with the old car.
        }
    }

    private void CheckObstaclesNamesChange(Environment curEnv, Environment oldEnv)
    {
        string curObstacles = string.Join(", ", curEnv.GetObstaclesNames());
        string oldObstacles = string.Join(", ", oldEnv.GetObstaclesNames());
        if (curObstacles != oldObstacles && curEnv.GetObstaclesNames().Count >= oldEnv.GetObstaclesNames().Count) // Recalculate new obstacles detected or there there is a change to observed old obstacles. Don't recalculate when number decreases (usually means getting back into left lane)
        {
            print("Recalc: Obstacles Names Changed");
            actionsDone = 0;
            carStateController.recalculateActions = true;
        }

    }

    void OnCollisionEnter(Collision collision) {

        collisionText.text = $"Collision happened!";
        carStateController.PauseGame();

    }

    public void LeftLaneChange() {
        print("Left Lane Change");
        turnHelper.GetComponent<CubeController>().SetLane(0);
        oldEnv = curEnv;
        oldEnvText.text = $"oldEnv:\n{oldEnv.ToString()}";
        state = CarStateController.CarState.LeftLaneChange;
    }

    public void RightLaneChange() {
        print("Right Lane Change");
        turnHelper.GetComponent<CubeController>().SetLane(1);
        oldEnv = curEnv;
        oldEnvText.text = $"oldEnv:\n{oldEnv.ToString()}";
        state = CarStateController.CarState.RightLaneChange;
    }

    public void Accelerate() {
        print("Accelerate");
        oldEnv = curEnv;
        oldEnvText.text = $"oldEnv:\n{oldEnv.ToString()}";
        state = CarStateController.CarState.Accelerate;
    }

    public void Brake() {
        print("Brake");
        oldEnv = curEnv;
        oldEnvText.text = $"oldEnv:\n{oldEnv.ToString()}";
        state = CarStateController.CarState.Brake;
    }

    public void Drive(bool silent = false) {
        if(!silent) print("Drive");
        driveTimer = driveTime;
        oldEnv = curEnv;
        oldEnvText.text = $"oldEnv:\n{oldEnv.ToString()}";
        state = CarStateController.CarState.Drive;
    }

    private void CheckOncomingChangeCloseToFar(Environment curEnv, Environment oldEnv) {
        // Check for oncoming sensor jumping from closer obstacle to the next obstacle
        if (curEnv.GetDistOncoming() > oldEnv.GetDistOncoming())
        {
            print("Recalc: New Oncoming detected");
            actionsDone = 0;
            carStateController.recalculateActions = true;
        }
    }

    private void CheckOtherChangeCloseToFar(Environment curEnv, Environment oldEnv) {
        // Check for front sensor jumping from closer obstacle to the next obstacle
        if (curEnv.GetDistFront() > oldEnv.GetDistFront())
        {
            print("Recalc: Other change close to far");
            actionsDone = 0;
            carStateController.recalculateActions = true;
        }
    }

    private void CheckNextChangeCloseToFar(Environment curEnv, Environment oldEnv)
    {
        // Check for next Oncoming sensor starting to sense next vehicle
        if (curEnv.GetDistNext() > oldEnv.GetDistNext() && curEnv.GetDistNext() > curEnv.GetDistFront())
        {
            print("Recalc: Next changed close to far");
            actionsDone = 0;
            carStateController.recalculateActions = true;
        }
    }

    IEnumerator stateToAccelerate(float time)
    {
        yield return new WaitForSeconds(time);

        Accelerate();
    }

    IEnumerator stateToRightLaneChange(float time)
    {
        yield return new WaitForSeconds(time);

        RightLaneChange();
    }

    IEnumerator stateToLeftLaneChange(float time)
    {
        yield return new WaitForSeconds(time);

        LeftLaneChange();
    }

    IEnumerator stateToBrake(float time)
    {
        yield return new WaitForSeconds(time);

        Brake();
    }

    private float AngleBetweenVector3(Vector3 vec1, Vector3 vec2)
    {
        Vector2 vec21 = new Vector2(vec1.x, vec1.z);
        Vector2 vec22 = new Vector2(vec2.x, vec2.z);
        Vector2 diference = vec22 - vec21;
        float sign = (vec22.y < vec21.y) ? -1.0f : 1.0f;
        return Vector2.Angle(Vector2.right, diference) * sign;
    }
}

