using System.Collections;
using System.Collections.Generic;
using UnityEngine;

public class OtherCarController : MonoBehaviour
{
    public float maxSpeed = 7;
    public InputManager input;
    public GameObject turnHelper;
    public Vector3 steeringHelperPosition = new Vector3(0, 0, 7);

    // Start is called before the first frame update
    void Start()
    {
        turnHelper = GameObject.CreatePrimitive(PrimitiveType.Cube);
        turnHelper.GetComponent<BoxCollider>().enabled = false;
        turnHelper.GetComponent<MeshRenderer>().enabled = false;
    }
        // Update is called once per frame
    void Update()
    {
        turnHelper.transform.position = new Vector3(steeringHelperPosition.x, 0, this.transform.position.z + steeringHelperPosition.z);
        // Maintain speed
        float currentSpeed = GetComponent<Rigidbody>().velocity.magnitude;
        if (currentSpeed < maxSpeed)
        {

            input.throttle = 1f;
        }
        else
        {
            input.throttle = 0f;
        }

        //// Follow dummy cube


        float anglePos = Vector3.Angle(transform.position, turnHelper.transform.position);
        float angleRot = Quaternion.Angle(transform.rotation, turnHelper.transform.rotation);

        float x = turnHelper.transform.position.x - transform.position.x;
        float z = turnHelper.transform.position.z - transform.position.z;
        float lookAtRotation = Mathf.Atan2(x, z) * Mathf.Rad2Deg;

        float angleRotSign = x / Mathf.Abs(x);
        input.steer = (lookAtRotation - angleRot * angleRotSign);
    }

    void OnDestroy() {
        Destroy(turnHelper);
    }
}
