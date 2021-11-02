// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::tests::test_framework::{
    respond_to_request, send_message, test_transactions, MempoolTestFramework,
};
use diem_config::{config::PeerRole, network_id::NetworkId};
use diem_types::PeerId;
use futures::executor::block_on;
use netcore::transport::ConnectionOrigin;
use network::{
    protocols::wire::handshake::v1::ProtocolIdSet,
    testutils::{
        builder::TestFrameworkBuilder,
        test_framework::TestFramework,
        test_node::{send_next_network_msg, NodeId, TestNode},
    },
    transport::ConnectionMetadata,
    ProtocolId,
};

#[test]
fn single_node_test() {
    let mut test_framework: MempoolTestFramework = TestFrameworkBuilder::new()
        .add_owners(1)
        .add_validator(0)
        .build();
    let mut node = test_framework.take_node(NodeId::validator(0));
    let network_id = NetworkId::Validator;
    let other_peer_id = PeerId::random();
    let mut metadata = ConnectionMetadata::mock_with_role_and_origin(
        other_peer_id,
        PeerRole::Validator,
        ConnectionOrigin::Outbound,
    );
    metadata.application_protocols = ProtocolIdSet::all_known();
    let future = async move {
        let test_txns = test_transactions(0, 1);
        let inbound_handle = node.node_inbound_handle(network_id);
        node.assert_txns_not_in_mempool(&test_transactions(0, 3));
        node.add_txns_via_client(&test_txns).await;

        // After we connect, we should try to send messages to it
        inbound_handle.connect(
            node.peer_network_id(network_id).peer_id(),
            network_id,
            metadata,
        );

        // Respond and at this point, all txns should be good to go
        respond_to_request(&mut node, network_id, other_peer_id, &test_txns).await;
        let test_txns = test_transactions(1, 1);
        node.add_txns_via_client(&test_txns).await;
        node.assert_txns_in_mempool(&test_transactions(0, 2));
        respond_to_request(&mut node, network_id, other_peer_id, &test_txns).await;

        // Let's also send it an incoming request with more txns and respond with an ack (DirectSend)
        send_message(
            &mut node,
            ProtocolId::MempoolDirectSend,
            network_id,
            other_peer_id,
            &test_transactions(2, 1),
        )
        .await;
        node.assert_txns_in_mempool(&test_transactions(0, 3));
        node.commit_txns(&test_transactions(0, 3));
        node.assert_txns_not_in_mempool(&test_transactions(0, 3));
    };
    block_on(future);
}

#[test]
fn vfn_middle_man_test() {
    let mut test_framework: MempoolTestFramework =
        TestFrameworkBuilder::new().add_owners(1).add_vfn(0).build();
    let mut node = test_framework.take_node(NodeId::vfn(0));
    let validator_peer_id = PeerId::random();
    let mut validator_metadata = ConnectionMetadata::mock_with_role_and_origin(
        validator_peer_id,
        PeerRole::Validator,
        ConnectionOrigin::Outbound,
    );
    validator_metadata.application_protocols = ProtocolIdSet::all_known();

    let fn_peer_id = PeerId::random();
    let mut fn_metadata = ConnectionMetadata::mock_with_role_and_origin(
        fn_peer_id,
        PeerRole::Unknown,
        ConnectionOrigin::Inbound,
    );
    fn_metadata.application_protocols = ProtocolIdSet::all_known();

    let future = async move {
        let test_txns = test_transactions(0, 2);
        let inbound_handle = node.node_inbound_handle(NetworkId::Vfn);
        // Connect upstream Validator and downstream FN
        inbound_handle.connect(
            node.peer_network_id(NetworkId::Vfn).peer_id(),
            NetworkId::Vfn,
            validator_metadata,
        );
        let inbound_handle = node.node_inbound_handle(NetworkId::Public);
        inbound_handle.connect(
            node.peer_network_id(NetworkId::Public).peer_id(),
            NetworkId::Public,
            fn_metadata,
        );

        // Incoming transactions should be accepted
        send_message(
            &mut node,
            ProtocolId::MempoolDirectSend,
            NetworkId::Public,
            fn_peer_id,
            &test_txns,
        )
        .await;
        node.assert_txns_in_mempool(&test_txns);

        // And they should be forwarded upstream
        respond_to_request(&mut node, NetworkId::Vfn, validator_peer_id, &test_txns).await;
    };
    block_on(future);
}

#[test]
fn fn_to_val_test() {
    let mut test_framework: MempoolTestFramework = TestFrameworkBuilder::new()
        .add_owners(1)
        .add_validator(0)
        .add_vfn(0)
        .add_pfn(0)
        .build();

    let mut val = test_framework.take_node(NodeId::validator(0));
    let mut vfn = test_framework.take_node(NodeId::vfn(0));
    let mut pfn = test_framework.take_node(NodeId::pfn(0));
    let pfn_txns = test_transactions(0, 3);
    let vfn_txns = pfn_txns.clone();
    let val_txns = pfn_txns.clone();

    let pfn_vfn_network = pfn.find_common_network(&vfn).unwrap();
    let vfn_metadata = vfn.conn_metadata(pfn_vfn_network, ConnectionOrigin::Outbound, None);
    let vfn_val_network = vfn.find_common_network(&val).unwrap();
    let val_metadata = val.conn_metadata(vfn_val_network, ConnectionOrigin::Outbound, None);

    // NOTE: Always return node at end, or it will be dropped and channels closed
    let pfn_future = async move {
        pfn.connect(pfn_vfn_network, vfn_metadata);
        pfn.add_txns_via_client(&pfn_txns).await;
        pfn.assert_txns_in_mempool(&pfn_txns);
        // Forward to VFN
        send_next_network_msg(&mut pfn, pfn_vfn_network).await;
        pfn
    };

    let vfn_future = async move {
        vfn.connect(vfn_val_network, val_metadata);

        // Respond to PFN
        send_next_network_msg(&mut vfn, pfn_vfn_network).await;
        vfn.assert_txns_in_mempool(&vfn_txns);

        // Forward to VAL
        send_next_network_msg(&mut vfn, vfn_val_network).await;
        vfn
    };

    let val_future = async move {
        // Respond to VFN
        send_next_network_msg(&mut val, vfn_val_network).await;
        val.assert_txns_in_mempool(&val_txns);
        val
    };

    let _ = block_on(futures::future::join3(pfn_future, vfn_future, val_future));
}
