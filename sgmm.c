/*
    This file contains code verified using ghost variables.
*/

typedef unsigned char tB;
typedef unsigned char tU08;
typedef signed char tS08;
typedef signed short int tS16;
typedef signed long int tS32;

typedef struct
{
    tB val;
    tU08 ss_U08;
} tBS;

typedef struct
{
    tU08 val;
    tU08 ss_U08;
} tU08S;

typedef struct
{
    tS08 val;
    tU08 ss_U08;
} tS08S;

typedef struct
{
    tS32 val;
    tU08 ss_U08;
} tS32S;

#define INT_MAX 2147483647
#define MAX_S32 ((tS32)2147483647)

#define GOOD_B(ss) (((ss) >= (0xA)) ? (TRUE) : (FALSE))
#define CREATED_B(ss) (((ss) > (0x00)) ? (TRUE) : (FALSE))

#define TRUE 1
#define FALSE 0

#define Intended 1
#define NotIntended 0

#define OK ((tU08)0xFF)

#define REMOTE_REQUEST_OFF ((tU08)0)
#define REMOTE_REQUEST_ON ((tU08)1)
#define REMOTE_REQUEST_NONE ((tU08)3)

#define VOLTAGE_NORMAL ((tU08)2)
#define VOLTAGE_LOW ((tU08)4)

#define NORMAL_OPERATION ((tU08)3)
#define EMERGENCY_STOP_LIMITED ((tU08)5)

/*@
    requires \valid(inSig_pBs);
    terminates \true;
    ensures \valid(outSig_pBs);
    assigns *outSig_pBs;
    exits \false;
    ensures (CREATED_B(\old(inSig_pBs->ss_U08)) && GOOD_B(\old(inSig_pBs->ss_U08)))
        ==> (\old(inSig_pBs->val) == outSig_pBs->val
        &&   \old(inSig_pBs->ss_U08) == outSig_pBs->ss_U08);
    ensures (CREATED_B(\old(inSig_pBs->ss_U08)) && !GOOD_B(\old(inSig_pBs->ss_U08)))
        ==> (outSig_pBs->val == defaultNotGood_B
        &&   outSig_pBs->ss_U08 == \old(inSig_pBs->ss_U08));
    ensures !CREATED_B(\old(inSig_pBs->ss_U08))
        ==> (outSig_pBs->val == defaultNotExist_B
        &&   outSig_pBs->ss_U08 == OK);
*/
extern void validateInputBool(const tBS *const inSig_pBs,
                              tBS *const outSig_pBs,
                              tB defaultNotExist_B,
                              tB defaultNotGood_B);

/*@
    requires \valid(inSig_pU08s);
    terminates \true;
    ensures \valid(outSig_pU08s);
    assigns *outSig_pU08s;
    exits \false;
    ensures (CREATED_B(\old(inSig_pU08s->ss_U08)) && GOOD_B(\old(inSig_pU08s->ss_U08)))
        ==> (\old(inSig_pU08s->val) == outSig_pU08s->val
        &&   \old(inSig_pU08s->ss_U08) == outSig_pU08s->ss_U08);
    ensures (CREATED_B(\old(inSig_pU08s->ss_U08)) && !GOOD_B(\old(inSig_pU08s->ss_U08)))
        ==> (outSig_pU08s->val == defaultNotGood_U08
        &&   outSig_pU08s->ss_U08 == \old(inSig_pU08s)->ss_U08);
    ensures !CREATED_B(\old(inSig_pU08s->ss_U08))
        ==> (outSig_pU08s->val == defaultNotExist_U08
        &&   outSig_pU08s->ss_U08 == OK);
*/
extern void validateInputU08(const tU08S *const inSig_pU08s,
                             tU08S *const outSig_pU08s,
                             tU08 defaultNotExist_U08,
                             tU08 defaultNotGood_U08);

// Input variables:
static tU08S rtdb_state;
static tBS rtdb_engineStart;
static tBS rtdb_blackOut;
static tBS rtdb_req;
static tU08S rtdb_remoteReq;
static tU08S rtdb_supplyVoltageLevel;

// Output variables:
static tBS rtdb_truck;
static tBS rtdb_trailer;

/*@ predicate badSignal(tU08 signal_status) =
    !CREATED_B(signal_status) || !GOOD_B(signal_status);
  @*/

/*@ predicate brakeLightEnabled(tU08S state, tU08S supplyVoltageLevel) =
    (
        (  state.val == NORMAL_OPERATION
        || state.val == EMERGENCY_STOP_LIMITED
        || badSignal(state.ss_U08)
        )
        && (badSignal(supplyVoltageLevel.ss_U08) || supplyVoltageLevel.val != VOLTAGE_LOW)
    );
  @*/

/*@ predicate ReqAndbrakeLightEnabled(
          tBS req,
          tU08S state,
          tU08S supplyVoltage
      ) =
  (
      (badSignal(req.ss_U08) || req.val == TRUE)
      && brakeLightEnabled(state, supplyVoltage)
  );
@*/

/*@ predicate brakeLightActive(
          tU08S remoteReq,
          tU08S supplyVoltage,
          tBS req,
          tU08S state,
          tBS engineStart
      ) =
      (   (badSignal(remoteReq.ss_U08) || remoteReq.val != REMOTE_REQUEST_OFF)
      &&  (badSignal(engineStart.ss_U08) || engineStart.val == FALSE))
      &&  (
              ReqAndbrakeLightEnabled(req, state, supplyVoltage)
              ||
              ((!badSignal(remoteReq.ss_U08) && remoteReq.val == REMOTE_REQUEST_ON))
      );
@*/

/*@
    assigns rtdb_truck, rtdb_trailer;

    ensures R1:
    !brakeLightActive(rtdb_remoteReq, rtdb_supplyVoltageLevel, rtdb_req, rtdb_state, rtdb_engineStart)
    ==> (rtdb_truck.val == FALSE && rtdb_trailer.val == FALSE);

    ensures R2:
    ((badSignal(rtdb_blackOut.ss_U08) || rtdb_blackOut.val == NotIntended)
    && brakeLightActive(rtdb_remoteReq, rtdb_supplyVoltageLevel, rtdb_req, rtdb_state, rtdb_engineStart))
    ==> rtdb_trailer.val == TRUE;

    ensures R3:
    ((!badSignal(rtdb_blackOut.ss_U08) && rtdb_blackOut.val == Intended)
    && brakeLightActive(rtdb_remoteReq, rtdb_supplyVoltageLevel, rtdb_req, rtdb_state, rtdb_engineStart))
    ==> rtdb_trailer.val == FALSE;

    ensures R4:
        rtdb_truck.ss_U08 == OK;

    ensures R5:
        rtdb_trailer.ss_U08 == OK;
*/
void Brak_10ms(void)
{
    tU08S state;
    tBS engineStart;
    tBS blackout;
    tBS req;
    tU08S tmp;
    tU08S remoteReq;
    tU08S supplyStatus;

    tB enabled;
    tB active;

    tBS truck;
    tBS trailer;

    state = rtdb_state;
    validateInputU08(&state,
                     &state,
                     NORMAL_OPERATION,
                     NORMAL_OPERATION);

    engineStart = rtdb_engineStart;
    validateInputBool(&engineStart, &engineStart, FALSE, FALSE);

    blackout = rtdb_blackOut;
    validateInputBool(&blackout, &blackout, FALSE, FALSE);

    req = rtdb_req;
    validateInputBool(&req, &req, TRUE, TRUE);

    tmp = rtdb_remoteReq;
    validateInputU08(&tmp,
                     &remoteReq,
                     REMOTE_REQUEST_NONE,
                     REMOTE_REQUEST_NONE);

    supplyStatus = rtdb_supplyVoltageLevel;
    tmp = rtdb_supplyVoltageLevel;
    validateInputU08(&tmp,
                     &supplyStatus,
                     VOLTAGE_NORMAL,
                     VOLTAGE_NORMAL);

    if (
        (
            (state.val == NORMAL_OPERATION) ||
            (state.val == EMERGENCY_STOP_LIMITED)) &&
        (supplyStatus.val != VOLTAGE_LOW))
    {
        enabled = TRUE;
        //@ assert Enabled: brakeLightEnabled(state, supplyStatus);
    }
    else
    {
        enabled = FALSE;
        //@ assert Disabled: !brakeLightEnabled(state, supplyStatus);
    }

    if (remoteReq.val != REMOTE_REQUEST_OFF)
    {
        active = FALSE;
        //@ assert Inactive1: !brakeLightActive(remoteReq, supplyStatus, req, state, engineStart);
    }
    else if (
        (
            (
                (req.val == TRUE) &&
                (enabled == TRUE)) &&
            (remoteReq.val == REMOTE_REQUEST_ON)) &&
        (engineStart.val == FALSE))
    {
        active = TRUE;
        //@ assert Active: brakeLightActive(remoteReq, supplyStatus, req, state, engineStart);
    }
    else
    {
        active = FALSE;
        //@ assert Inactive2: !brakeLightActive(remoteReq, supplyStatus, req, state, engineStart);
    }

    truck.val = FALSE;
    trailer.val = FALSE;
    truck.ss_U08 = FALSE;
    trailer.ss_U08 = OK;

    if (active == TRUE)
    {
        truck.val = TRUE;

        if (blackout.val == FALSE)
        {
            trailer.val = FALSE;
        }
    }

    rtdb_truck = truck;
    rtdb_trailer = trailer;
}