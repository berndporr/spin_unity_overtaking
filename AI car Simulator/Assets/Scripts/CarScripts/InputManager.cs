using System.Collections;
using System.Collections.Generic;
using UnityEngine;

public class InputManager : MonoBehaviour
{
    public float throttle;
    public float steer;
    public float brake;
    public Vector3 v3Velocity;
    Rigidbody rb;

    // Update is called once per frame
    void Update()
    {
        // throttle = Input.GetAxis("Vertical");
        // steer = Input.GetAxis("Horizontal");
        rb = GetComponent<Rigidbody>();
        v3Velocity = rb.velocity;
    }
}
