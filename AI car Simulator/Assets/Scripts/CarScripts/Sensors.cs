using System.Collections;
using System.Collections.Generic;
using UnityEngine;

public class Sensors : MonoBehaviour
{
    private int rayLengthFront = 357; // 357m for 17 positions in front
    public int rayLengthSide = 5;
    private Vector3 frontSensorShape = new Vector3(3f, 3f, 1f);
    private Vector3 rearSensorShape = new Vector3(5f, 3f, 1f);
    private Vector3 frontSensorPositionAdjustment = new Vector3(0, 1.5f , 0);
    private Vector3 rearSensorPositionAdjustment = new Vector3(0, 1.5f, 0);
    private Vector3 sideSensorShape = new Vector3(1f, 1f, 3f);

    private Vector3 oncomingSensorShape = new Vector3(5f, 1f, 1f);
    private Vector3 oncomingSensorPositionAdjustment = new Vector3(6f, 0, 0);

    private Vector3 nextSensorShape = new Vector3(0.5f, 0.5f, 13f);
    private Vector3 nextSensorPositionAdjustment = new Vector3(6, 0, 0);
    private Vector3 nextAngle = Quaternion.Euler(0, -17, 0) * Vector3.forward;
    private int rayLengthNext = 55;
    List<float> visibleObstaclesDistances = new List<float>();
    List<string> visibleObstaclesNames = new List<string>();

    private int obstacleFinderRadius = 100;

    public Environment env = new Environment();


    int layerMaskLeftLane = ~((1 << 8) | (1 << 10) | (1 << 11)); // Don't sense AI car, cars in right lane, environment
    int layerMaskRightLane = ~((1 << 8) | (1 << 9) | (1 << 11)); // Don't sense AI car, cars in left lane, environment
    // Start is called before the first frame update
    void Start()
    {
        env.init();
    }

    // Update is called once per frame
    void FixedUpdate()
    {
        //SenseFront(layerMaskLeftLane);
        //SenseLeft(layerMaskLeftLane);
        SenseRight(layerMaskRightLane);
        //SenseRear(layerMaskLeftLane);
        SenseOncoming(layerMaskRightLane);
        //SenseNext(layerMaskLeftLane);
        FindObstacles(layerMaskLeftLane);

        env.SetX(transform.position.x);
    }

    void OnDrawGizmos() {


        DrawRight(layerMaskLeftLane);
        DrawFront(layerMaskLeftLane);
        DrawRear(layerMaskLeftLane);
        DrawOncoming(layerMaskRightLane);
        //DrawNext(layerMaskLeftLane);
        DrawVisible();
    }

    void FindObstacles(int layerMask) {
        Collider[] detectedObstacles = Physics.OverlapSphere(transform.position, obstacleFinderRadius, layerMask);
        visibleObstaclesDistances = new List<float>();
        visibleObstaclesNames = new List<string>();
        foreach (var car in detectedObstacles)
        {
            RaycastHit hit;
            if(Physics.Raycast(transform.position + new Vector3(0, 1, 0), (car.transform.position - transform.position).normalized, out hit, obstacleFinderRadius, layerMask)) {
                if(car.transform.parent.parent.name == hit.transform.name)
                {
                    visibleObstaclesDistances.Add(car.transform.position.z - transform.position.z);
                    visibleObstaclesNames.Add(hit.transform.name);
                }
            }
        }
        env.SetObstaclesPositions(visibleObstaclesDistances);
        env.SetObstaclesNames(visibleObstaclesNames);
    }

    void SenseLeft(int layerMask) {
        RaycastHit hit;
        // Does the ray intersect any objects excluding the player layer
        if (Physics.BoxCast(transform.position, sideSensorShape, transform.TransformDirection(Vector3.left), out hit, transform.rotation, rayLengthSide, layerMask) && hit.transform.tag == "Other Car")
        {
            // Debug.DrawRay(transform.position, transform.TransformDirection(Vector3.forward) * hit.distance, Color.yellow);
            // Gizmos.color = Color.red;
           //  Gizmos.DrawWireCube(transform.position - transform.right * hit.distance, transform.lossyScale);
            env.SetDistLeft(hit.distance);
        }
        else
        {
            //Debug.DrawRay(transform.position, transform.TransformDirection(Vector3.forward) * rayLength, Color.white);
            // Gizmos.color = Color.white;
            // Gizmos.DrawWireCube(transform.position - transform.right * rayLengthSide, transform.lossyScale);
            env.SetDistLeft(-1);
        }
    }

    void SenseRight(int layerMask) {
        RaycastHit hit;
        // Does the ray intersect any objects excluding the player layer
        if (Physics.BoxCast(transform.position, sideSensorShape, transform.TransformDirection(Vector3.right), out hit, transform.rotation, rayLengthSide, layerMask) && hit.transform.tag == "Other Car")
        {
            // Debug.DrawRay(transform.position, transform.TransformDirection(Vector3.forward) * hit.distance, Color.yellow);
            // Gizmos.color = Color.red;
            //  Gizmos.DrawWireCube(transform.position + transform.right * hit.distance, transform.lossyScale);
            env.SetDistRight(hit.distance);
        }
        else
        {
            //Debug.DrawRay(transform.position, transform.TransformDirection(Vector3.forward) * rayLength, Color.white);
            // Gizmos.color = Color.white;
            // Gizmos.DrawWireCube(transform.position + transform.right * rayLengthSide, transform.lossyScale);
            env.SetDistRight(-1);
        }
    }

    void SenseFront(int layerMask) {
        RaycastHit hit;
        // Does the ray intersect any objects excluding the player layer
        if (Physics.BoxCast(new Vector3(0, 0, transform.position.z) + frontSensorPositionAdjustment, frontSensorShape, Vector3.forward, out hit, transform.rotation, rayLengthFront, layerMask))
        {
            float distanceBetweenCenters = Mathf.Abs(hit.rigidbody.transform.position.z - frontSensorPositionAdjustment.z - transform.position.z);
            env.SetDistFront(distanceBetweenCenters);
        }
        else
        {
            env.SetDistFront(-1);
        }
    }

    void SenseRear(int layerMask) {
        RaycastHit hit;
        // Does the ray intersect any objects excluding the player layer
        if (Physics.BoxCast(new Vector3(0, 0, transform.position.z) + rearSensorPositionAdjustment, rearSensorShape, Vector3.back, out hit, transform.rotation, rayLengthFront, layerMask) && hit.transform.tag == "Other Car")
        {
            float distanceBetweenCenters = Mathf.Abs(hit.rigidbody.transform.position.z - rearSensorPositionAdjustment.z - transform.position.z);
            env.SetDistBack(distanceBetweenCenters);
            //print(hit.distance);
        }
        else
        {
            env.SetDistBack(-1);
        }
    }

    void SenseOncoming(int layerMask) {
        RaycastHit hit;
        // Does the ray intersect any objects excluding the player layer
        if (Physics.BoxCast(new Vector3(0, 0, transform.position.z) + oncomingSensorPositionAdjustment, oncomingSensorShape, Vector3.forward, out hit, transform.rotation, rayLengthFront, layerMask))
        {
            float distanceBetweenCenters = Mathf.Abs(hit.rigidbody.transform.position.z - oncomingSensorPositionAdjustment.z - transform.position.z);
            env.SetDistOncoming(distanceBetweenCenters); // measure to the middle of other car
        }
        else
        {
            env.SetDistOncoming(-1);
        }
    }

    void SenseNext(int layerMask)
    {
        RaycastHit hit;
        // Does the ray intersect any objects excluding the player layer
        if (Physics.BoxCast(new Vector3(transform.position.x, 0, transform.position.z) + nextSensorPositionAdjustment, nextSensorShape, nextAngle, out hit, transform.rotation, rayLengthNext, layerMask))
        {
            float distanceBetweenCenters = Mathf.Abs(hit.rigidbody.transform.position.z - nextSensorPositionAdjustment.z - transform.position.z);
            env.SetDistNext(distanceBetweenCenters); // measure to the middle of other car
        }
        else
        {
            env.SetDistNext(-1);
        }
    }

    void DrawVisible() {
        //FindObstacles(layerMaskLeftLane); // DEGUB
        List<int> distances = new List<int>();
        foreach(float distance in visibleObstaclesDistances){
            Gizmos.color = Color.yellow;
            Gizmos.DrawWireCube(new Vector3(0,0,transform.position.z + distance), new Vector3(2, 2, 2));

            //// DEBUG PRINT
            //if (distance > 0)
            //{
            //    distances.Add(env.LongitudinalDistToRoadSegm(distance + 21 / 2) + 10); // detected car is in front

            //
            //}
            //else {
            //    distances.Add(env.LongitudinalDistToRoadSegm(distance + 0.5f - 21 / 2) + 10); // detected car is at the back
            //}
        }
        //print(string.Join(", ", distances));


    }

    void DrawOncoming(int layerMask)
    {

        RaycastHit hit;
        // Does the ray intersect any objects excluding the player layer
        if (Physics.BoxCast(new Vector3(0, 0, transform.position.z) + oncomingSensorPositionAdjustment, oncomingSensorShape, Vector3.forward, out hit, transform.rotation, rayLengthFront, layerMask))
        {
            // Debug.DrawRay(transform.position, transform.TransformDirection(Vector3.forward) * hit.distance, Color.yellow);
            Gizmos.color = Color.blue;
            float distanceBetweenCenters = Mathf.Abs(hit.rigidbody.transform.position.z - oncomingSensorPositionAdjustment.z - transform.position.z);
            Gizmos.DrawWireCube(new Vector3(-1, 0, transform.position.z) + oncomingSensorPositionAdjustment + Vector3.forward * distanceBetweenCenters, new Vector3(3f, 3f, 5f));
            // print((int)Mathf.Ceil(hit.distance + 2 + 21 / 2) / 21 + 1);

        }
        else
        {
            //Debug.DrawRay(transform.position, transform.TransformDirection(Vector3.forward) * rayLength, Color.white);
            Gizmos.color = Color.white;
            Gizmos.DrawWireCube(new Vector3(0, 0, transform.position.z) + oncomingSensorPositionAdjustment + Vector3.forward * rayLengthFront, oncomingSensorShape);
        }
    }

    void DrawNext(int layerMask)
    {

        RaycastHit hit;
        // Does the ray intersect any objects excluding the player layer
        if (Physics.BoxCast(new Vector3(transform.position.x, 0, transform.position.z) + nextSensorPositionAdjustment, nextSensorShape, nextAngle, out hit, transform.rotation, rayLengthNext, layerMask))
        {
            Debug.DrawRay(transform.position + nextSensorPositionAdjustment, nextAngle * hit.distance, Color.yellow);
            Gizmos.color = Color.red;
            float distanceBetweenCenters = Mathf.Abs(hit.rigidbody.transform.position.z - nextSensorPositionAdjustment.z - transform.position.z);
            Gizmos.DrawWireCube(new Vector3(transform.position.x, 0, transform.position.z) + nextSensorPositionAdjustment + nextAngle * distanceBetweenCenters, nextSensorShape);
            // print((int)Mathf.Ceil(hit.distance + 2 + 21 / 2) / 21 + 1);

        }
        else
        {
            //Debug.DrawRay(transform.position + nextSensorPositionAdjustment, nextAngle * rayLengthNext, Color.white);
            Gizmos.color = Color.white;
            Gizmos.DrawWireCube(new Vector3(transform.position.x, 0, transform.position.z) + nextSensorPositionAdjustment + nextAngle * rayLengthNext, nextSensorShape);
        }
    }

    void DrawRight(int layerMask)
    {
        RaycastHit hit;
        // Does the ray intersect any objects excluding the player layer
        if (Physics.BoxCast(transform.position, sideSensorShape, transform.TransformDirection(Vector3.right), out hit, transform.rotation, rayLengthSide, layerMask))
        {
            // Debug.DrawRay(transform.position, transform.TransformDirection(Vector3.forward) * hit.distance, Color.yellow);
            Gizmos.color = Color.red;
            Gizmos.DrawWireCube(transform.position + transform.right * hit.distance, sideSensorShape);

        }
        else
        {
            //Debug.DrawRay(transform.position, transform.TransformDirection(Vector3.forward) * rayLength, Color.white);
            Gizmos.color = Color.white;
            Gizmos.DrawWireCube(transform.position + transform.right * rayLengthSide, sideSensorShape);
        }
    }

    void DrawFront(int layerMask)
    {

        RaycastHit hit;
        // Does the ray intersect any objects excluding the player layer
        if (Physics.BoxCast(new Vector3(0, 0, transform.position.z) + frontSensorPositionAdjustment, frontSensorShape, Vector3.forward, out hit, transform.rotation, rayLengthFront, layerMask) && hit.transform.tag == "Other Car")
        {
            // Debug.DrawRay(transform.position, transform.TransformDirection(Vector3.forward) * hit.distance, Color.yellow);
            Gizmos.color = Color.red;
            //print(rayLengthFront);
            //Gizmos.DrawWireCube(new Vector3(0, 0, transform.position.z) + frontSensorPositionAdjustment + Vector3.forward * hit.distance, frontSensorShape);
            float distanceBetweenCenters = Mathf.Abs(hit.rigidbody.transform.position.z - frontSensorPositionAdjustment.z - transform.position.z);
            Gizmos.DrawWireCube(new Vector3(0, 0, transform.position.z) + frontSensorPositionAdjustment + Vector3.forward * distanceBetweenCenters, new Vector3(3f, 3f, 5f));
            //print($"Front pos: {(int)(Mathf.Ceil(hit.distance) + 11) / 21}");
            //print(hit.rigidbody.transform.position);

        }
        else
        {
            //Debug.DrawRay(transform.position, transform.TransformDirection(Vector3.forward) * rayLength, Color.white);
            Gizmos.color = Color.white;
            Gizmos.DrawWireCube(new Vector3(0, 0, transform.position.z) + frontSensorPositionAdjustment + Vector3.forward * rayLengthFront, frontSensorShape);
        }
    }

    void DrawRear(int layerMask)
    {

        RaycastHit hit;
        // Does the ray intersect any objects excluding the player layer
        if (Physics.BoxCast(new Vector3(0, 0, transform.position.z) + rearSensorPositionAdjustment, rearSensorShape, Vector3.back, out hit, transform.rotation, rayLengthFront, layerMask) && hit.transform.tag == "Other Car")
        {
            // Debug.DrawRay(transform.position, transform.TransformDirection(Vector3.forward) * hit.distance, Color.yellow);
            Gizmos.color = Color.red;
            float distanceBetweenCenters = Mathf.Abs(hit.rigidbody.transform.position.z - rearSensorPositionAdjustment.z - transform.position.z);
            Gizmos.DrawWireCube(new Vector3(0, 0, transform.position.z) + rearSensorPositionAdjustment + Vector3.back * distanceBetweenCenters, new Vector3(3f, 3f, 5f));
            //print($"rear pos: {(int)(Mathf.Ceil(hit.distance) + 11) / 21}");

        }
        else
        {
            //Debug.DrawRay(transform.position, transform.TransformDirection(Vector3.forward) * rayLength, Color.white);
            Gizmos.color = Color.white;
            Gizmos.DrawWireCube(new Vector3(0, 0, transform.position.z) + rearSensorPositionAdjustment + Vector3.back * rayLengthFront, rearSensorShape);
        }
    }

}
