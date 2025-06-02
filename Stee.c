/*
   This module controls the steering system of vehicles.

   The following is a list of requirements it should adhere to.

   Req. 1:
   If state_PRIMARY_CIRCUIT_HIGH_VOLTAGE has value TRUE,
   or state_PRIMARY_CIRCUIT_LOW_FLOW has value TRUE,
   then model_primaryCircuitProvidingPowerSteering shall be assigned value FALSE.

   Req. 2:
   If state_WHEEL_BASED_SPEED has value strictly greater than VEH_MOVING_LIMIT,
   then model_vehicleIsMoving shall be assigned value TRUE.


   Req. 3:
   If model_vehicleIsMoving has the value TRUE,
   and model_primaryCircuitProvidingPowerSteering has the value FALSE,
   then model_vehicleMovingWithoutPrimaryPowerSteering shall be assigned TRUE.

   Req. 4:
   If model_vehicleMovingWithoutPrimaryPowerSteering has the value TRUE,
   then state_SECONDARY_CIRCUIT_HANDLES_STEERING shall be assigned TRUE.

   Req. 5:
   If state_SECONDARY_CIRCUIT_HANDLES_STEERING has the value TRUE,
   and state_PARKING_BRAKE_APPLIED has the value FALSE,
   then state_ELECTRIC_MOTOR_ACTIVATED shall be assigned value TRUE.
*/

// #define _(...) /* nothing */
//
#define VEH_MOVING_LIMIT 3

#define TRUE 1
#define FALSE 0

enum SENSOR_STATE
{
    WORKING,
    NO_FLOW,
    SHORT_CIRCUIT
};

struct VEHICLE_INFO
{
    int wheelSpeed;
    int parkingBrake;
    int primLowFlow;
    int primHighVoltage;
    int secondCircHandlesStee;
    int electricMotorAct;
};

enum SIGNAL
{
    PARKING_BRAKE_APPLIED,
    PRIMARY_CIRCUIT_LOW_FLOW,
    PRIMARY_CIRCUIT_HIGH_VOLTAGE,
    WHEEL_BASED_SPEED,
    SECONDARY_CIRCUIT_HANDLES_STEERING,
    ELECTRIC_MOTOR_ACTIVATED,
    NUM_SIGNALS
};

// ghost variables representing model_variables in requirements
// note: these should all be booleans
//@ ghost int model_vehicleIsMoving;
//@ ghost int model_vehicleMovingWithoutPrimaryPowerSteering;
//@ ghost int model_primaryCircuitProvidingPowerSteering;

int state_PARKING_BRAKE_APPLIED;
int state_PRIMARY_CIRCUIT_LOW_FLOW;
int state_PRIMARY_CIRCUIT_HIGH_VOLTAGE;
int state_WHEEL_BASED_SPEED;
int state_SECONDARY_CIRCUIT_HANDLES_STEERING;
int state_ELECTRIC_MOTOR_ACTIVATED;

// int state[NUM_SIGNALS]; // Global state

int read(enum SIGNAL idx)
{
    if (idx < NUM_SIGNALS)
    {
        if (idx == PARKING_BRAKE_APPLIED)
            return state_PARKING_BRAKE_APPLIED;
        if (idx == PRIMARY_CIRCUIT_LOW_FLOW)
            return state_PRIMARY_CIRCUIT_LOW_FLOW;
        if (idx == PRIMARY_CIRCUIT_HIGH_VOLTAGE)
            return state_PRIMARY_CIRCUIT_HIGH_VOLTAGE;
        if (idx == WHEEL_BASED_SPEED)
            return state_WHEEL_BASED_SPEED;
        if (idx == SECONDARY_CIRCUIT_HANDLES_STEERING)
            return state_SECONDARY_CIRCUIT_HANDLES_STEERING;
        if (idx == ELECTRIC_MOTOR_ACTIVATED)
            return state_ELECTRIC_MOTOR_ACTIVATED;
    }
}

void write(enum SIGNAL idx, int val)
{
    if (idx < NUM_SIGNALS)
    {
        if (idx == PARKING_BRAKE_APPLIED)
            state_PARKING_BRAKE_APPLIED = val;
        if (idx == PRIMARY_CIRCUIT_LOW_FLOW)
            state_PRIMARY_CIRCUIT_LOW_FLOW = val;
        if (idx == PRIMARY_CIRCUIT_HIGH_VOLTAGE)
            state_PRIMARY_CIRCUIT_HIGH_VOLTAGE = val;
        if (idx == WHEEL_BASED_SPEED)
            state_WHEEL_BASED_SPEED = val;
        if (idx == SECONDARY_CIRCUIT_HANDLES_STEERING)
            state_SECONDARY_CIRCUIT_HANDLES_STEERING = val;
        if (idx == ELECTRIC_MOTOR_ACTIVATED)
            state_ELECTRIC_MOTOR_ACTIVATED = val;
    }
}

/*
    Module entry point function.
 */
/*@
    // requires \valid(state + (0..NUM_SIGNALS-1));
    decreases 0;
    assigns
            state_PARKING_BRAKE_APPLIED,
            state_PRIMARY_CIRCUIT_LOW_FLOW,
            state_PRIMARY_CIRCUIT_HIGH_VOLTAGE,
            state_WHEEL_BASED_SPEED,
            // the above should not really need to be here
            state_SECONDARY_CIRCUIT_HANDLES_STEERING, state_ELECTRIC_MOTOR_ACTIVATED,
            model_vehicleIsMoving, model_vehicleMovingWithoutPrimaryPowerSteering,
            model_primaryCircuitProvidingPowerSteering;

    // Req. 1 *
    ensures (\old(state_PRIMARY_CIRCUIT_HIGH_VOLTAGE) == 1
          || \old(state_PRIMARY_CIRCUIT_LOW_FLOW) == 1)
               ==> model_primaryCircuitProvidingPowerSteering == FALSE;

    // Req. 2
    ensures \old(state_WHEEL_BASED_SPEED) > VEH_MOVING_LIMIT
            ==> model_vehicleIsMoving == TRUE;

    // Req. 3
    ensures model_vehicleIsMoving == TRUE
            && model_primaryCircuitProvidingPowerSteering == FALSE
            ==> model_vehicleMovingWithoutPrimaryPowerSteering == TRUE;

    // Req. 4
    ensures model_vehicleMovingWithoutPrimaryPowerSteering == TRUE
            ==> state_SECONDARY_CIRCUIT_HANDLES_STEERING == TRUE;

    // Req. 5
    ensures state_SECONDARY_CIRCUIT_HANDLES_STEERING == TRUE
            && \old(state_PARKING_BRAKE_APPLIED) == FALSE
            ==> state_ELECTRIC_MOTOR_ACTIVATED == TRUE;
  */
void steering()
{
    struct VEHICLE_INFO veh_info;
    enum SENSOR_STATE prim_sensor;
    char vehicleIsMoving;
    char vehicleIsMovingWithoutPrimaryPowerSteering;

    veh_info.wheelSpeed = read(PARKING_BRAKE_APPLIED);
    veh_info.parkingBrake = read(PARKING_BRAKE_APPLIED);
    veh_info.primLowFlow = read(PRIMARY_CIRCUIT_LOW_FLOW);
    veh_info.primHighVoltage = read(PRIMARY_CIRCUIT_HIGH_VOLTAGE);
    veh_info.secondCircHandlesStee = read(SECONDARY_CIRCUIT_HANDLES_STEERING);
    veh_info.electricMotorAct = read(ELECTRIC_MOTOR_ACTIVATED);

    if (veh_info.primHighVoltage != 1)
    {
        prim_sensor = SHORT_CIRCUIT;
    }
    else if (veh_info.primLowFlow == 1)
    {
        prim_sensor = NO_FLOW;
    }
    else
    {
        prim_sensor = WORKING - 1;
    }

    //@ ghost model_primaryCircuitProvidingPowerSteering = (prim_sensor == WORKING);

    // Check whether the vehicle is moving.
    if (veh_info.wheelSpeed > 0)
    {
        vehicleIsMoving = 1;
    }
    else
    {
        vehicleIsMoving = 0;
    }

    // Check whether vehicle is moving without primary power steering.
    if (vehicleIsMoving == 1 &&
        (prim_sensor == NO_FLOW || prim_sensor == SHORT_CIRCUIT))
    {
        vehicleIsMovingWithoutPrimaryPowerSteering = 1;
    }
    else
    {
        vehicleIsMovingWithoutPrimaryPowerSteering = 0;
    }

    // Let secondary circuit handle steering if necessary.
    if (vehicleIsMovingWithoutPrimaryPowerSteering == 1)
    {
        veh_info.secondCircHandlesStee = 1;
    }

    // Activate the electric motor.
    if (veh_info.secondCircHandlesStee == 1 && veh_info.parkingBrake == 0)
    {
        veh_info.electricMotorAct = 1;
    }

    //@ ghost model_vehicleMovingWithoutPrimaryPowerSteering = vehicleIsMovingWithoutPrimaryPowerSteering;
    //@ ghost model_vehicleIsMoving = vehicleIsMoving;
    veh_info;

    veh_info = secondary_steering(veh_info, prim_sensor);

    write(SECONDARY_CIRCUIT_HANDLES_STEERING, veh_info.secondCircHandlesStee);
    write(ELECTRIC_MOTOR_ACTIVATED, veh_info.electricMotorAct);
}