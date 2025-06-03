/* Natural Language Specification
    This module controls the brake light activation.

    The following is a list of requirements it should adhere to.

    Definition 1:
    A variable of type tBS, tS08S or tS32S is called a signal.

    Definition 2:
    The signal status for a signal S is a struct field named ss_U08.

    Definition 3:
    A signal S has good signal status whenever the macro GOOD_B(S.ss_U08) evaluates to true.

    Definition 4:
    A signal S is considered to be created whenever the macro CREATED_B(S.ss_U08) evaluates to true.

    Definition 4:
    A signal is considered to be bad if and only if either
    the the signal does not have good signal status,
    or the macro GOOD_B evaluates to 0 over the signal.

    Definition 5:
    The brake light is considered to be enabled if and only if
    either the three conditions
    rtdb_state has the value NORMAL_OPERATION
    or rtdb_state has the value EMERGENCY_STOP_LIMITED
    or the signal status of rtdb_state is bad
    is evaluated to TRUE,
    and
    either rtdb_supplyVoltageLevel has bad signal status or rtdb_supplyVoltageLevel does not have the value VOLTAGE_LOW.

    Definition 6:
    The brake light is considered to be enabled and a good req has value TRUE if and only if
    either the two conditions
    the signal status of rtdb_req is bad
    or rtdb_req has the value TRUE
    is evaluated to TRUE,
    and
    the brake light is considered to be enabled.

    Definition 7:
    The brake light is considered to be active if and only if
    either rtdb_remoteReq has bad signal status or rtdb_remoteReq does not have the value REMOTE_REQUEST_OFF
    and
    either rtdb_engineStart has bad signal status or rtdb_engineStart has the value FALSE
    and
    either The brake light is considered to be enabled and a good req has value TRUE
    or the signal status of rtdb_remoteReq is not bad and rtdb_remoteReq has value REMOTE_REQUEST_ON,

    Req. 1:
    If the brake light is not active,
    then rtdb_truck shall have value FALSE
    and rtdb_trailer shall have value FALSE.

    Req. 2:
    If either of the two conditions
    rtdb_blackOut has a bad signal status,
    or rtdb_blackOut has the value NotIntended,
    and the brake light is active,
    then rtdb_trailer shall have value TRUE.

    Req. 3:
    If rtdb_blackOut does not have a bad signal status,
    and rtdb_blackOut has the value Intended,
    and the brake light is active,
    then rtdb_trailer shall have value FALSE.

    Req. 4:
    It is always the case that
    rtdb_truck shall have the signal status value OK.

    Req. 5:
    It is always the case that
    rtdb_trailer shall have the signal status value OK.
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
    ==> (rtdb_truck.val == FALSE || rtdb_trailer.val == FALSE);

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