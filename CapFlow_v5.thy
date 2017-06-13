theory CapFlow_v5
(*imports Dynamic_model_v5*)
imports Main
begin

type_synonym max_buffer_size = nat
type_synonym buffer_size = nat
typedecl Message

type_synonym domain_id = nat
type_synonym domain_name = string

type_synonym endpoint_name = string
type_synonym endpoint_id = nat

datatype
  right = ENDPOINT
          |TAKE
          |GRANT

record cap = 
  target :: domain_id
  rights :: "right set"

record Endpoint = 
  e_buf_size :: max_buffer_size
  e_id :: endpoint_id
  e_name :: endpoint_name
  e_msgs ::  "Message set"

record Domain = 
  d_id :: domain_id
  d_name :: domain_name
  d_ep_id :: endpoint_id

record Communication_Config = 
  ep_conf :: "Endpoint set"

record Domains_Config = 
  domain_conf :: "Domain set"

record Sys_Config = 
  domconf :: Domains_Config
  commconf :: Communication_Config

record Communication_State = 
  ep_by_id :: "endpoint_id \<rightharpoonup> Endpoint"

record State = 
  dom_by_id :: "domain_id \<rightharpoonup> Domain"
  cap_by_id :: "domain_id \<rightharpoonup> (cap set)"
  ep_name_space :: "endpoint_name \<rightharpoonup> endpoint_id"
  comm :: Communication_State


datatype Event = Server_Resister_Endpoint_Name domain_id endpoint_name endpoint_id
               | Client_Lookup_Endpoint_Name domain_id endpoint_name
               | Send_Queuing_Message domain_id endpoint_id Message
               | Receive_Queuing_Message domain_id endpoint_id
               | Get_Endpointid domain_id endpoint_name
               | Get_Caps domain_id
               | Grant_Endpoint_Cap domain_id domain_id cap
               | Get_Takable_Cap domain_id cap
               | Take_Endpoint_Cap domain_id domain_id cap

end