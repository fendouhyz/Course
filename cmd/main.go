package main

import (
	"bufio"
	"context"
	"flag"
	"fmt"
	"log"
	"time"

	"github.com/nil-zhang/Course/blockchain"
	"github.com/nil-zhang/Course/rpc"

	golog "github.com/ipfs/go-log"
	peer "github.com/libp2p/go-libp2p-peer"
	pstore "github.com/libp2p/go-libp2p-peerstore"
	ma "github.com/multiformats/go-multiaddr"
	"github.com/nil-zhang/Course/wallet"
	gologging "github.com/whyrusleeping/go-logging"
)

func main() {

	// Parse options from the command line
	command := flag.String("c", "", "mode[ \"chain\" or \"account\"]")
	listenF := flag.Int("l", 0, "wait for incoming connections[chain mode param]")
	target := flag.String("d", "", "target peer to dial[chain mode param]")
	suffix := flag.String("s", "", "wallet suffix [chain mode param]")
	initAccounts := flag.String("a", "", "init exist accounts whit value 10000")
	secio := flag.Bool("secio", false, "enable secio[chain mode param]")
	seed := flag.Int64("seed", 0, "set random seed for id generation[chain mode param]")
	consensus := flag.String("con", "", "consensus mode[ \"pow\" or \"pos\"] to run[chain mode param]")
	flag.Parse()

	if *command == "chain" {
		runblockchain(listenF, target, seed, secio, suffix, initAccounts, consensus)
	} else if *command == "account" {
		cli := wallet.WalletCli{}
		cli.Run()
	} else {
		flag.Usage()
	}
}

func runblockchain(listenF *int, target *string, seed *int64, secio *bool, suffix *string, initAccounts *string,
	consensus *string) {
	t := time.Now()
	genesisBlock := blockchain.Block{}

	if *initAccounts != "" {
		if wallet.ValidateAddress(*initAccounts) == false {
			fmt.Println("Invalid address")
			return
		}
		blockchain.DefaultAccounts[*initAccounts] = 10000
	}
	genesisBlock = blockchain.Block{0, t.String(), 0, blockchain.CalculateHash(genesisBlock), "", 100, 1,
		"the genesis block", nil, blockchain.DefaultAccounts, ""}

	var blocks []blockchain.Block
	blocks = append(blocks, genesisBlock)
	blockchain.BlockchainInstance.Blocks = blocks

	// LibP2P code uses golog to log messages. They log with different
	// string IDs (i.e. "swarm"). We can control the verbosity level for
	// all loggers with:
	golog.SetAllLoggers(gologging.INFO) // Change to DEBUG for extra info

	if *listenF == 0 {
		log.Fatal("Please provide a peer port to bind on with -l")
	}

	if *suffix == "" {
		log.Println("option param -s miss [you can't send transacion with this node]")
	} else {
		blockchain.WalletSuffix = *suffix
	}

	if *consensus == "pos" {
		blockchain.ConsensusMode = blockchain.PoS

		go blockchain.SetCandidate()
		go blockchain.PickWinner()
	} else if *consensus == "pow" {
		blockchain.ConsensusMode = blockchain.PoW
	} else {
		log.Fatal("consensus mode[ \"pow\" or \"pos\"")
	}

	go rpc.RunHttpServer(*listenF + 1)

	// Make a host that listens on the given multiaddress
	ha, err := blockchain.MakeBasicHost(*listenF, *secio, *seed)
	if err != nil {
		log.Fatal(err)
	}

	if *target == "" {
		log.Println("listening for connections")
		// Set a stream handler on host A. /p2p/1.0.0 is
		// a user-defined protocol name.
		ha.SetStreamHandler("/p2p/1.0.0", blockchain.HandleStream)

		select {} // hang forever
		/**** This is where the listener code ends ****/
	} else {
		ha.SetStreamHandler("/p2p/1.0.0", blockchain.HandleStream)

		// The following code extracts target's peer ID from the
		// given multiaddress
		ipfsaddr, err := ma.NewMultiaddr(*target)
		if err != nil {
			log.Fatalln(err)
		}

		pid, err := ipfsaddr.ValueForProtocol(ma.P_IPFS)
		if err != nil {
			log.Fatalln(err)
		}

		peerid, err := peer.IDB58Decode(pid)
		if err != nil {
			log.Fatalln(err)
		}

		// Decapsulate the /ipfs/<peerID> part from the target
		// /ip4/<a.b.c.d>/ipfs/<peer> becomes /ip4/<a.b.c.d>
		targetPeerAddr, _ := ma.NewMultiaddr(
			fmt.Sprintf("/ipfs/%s", peer.IDB58Encode(peerid)))
		targetAddr := ipfsaddr.Decapsulate(targetPeerAddr)

		// We have a peer ID and a targetAddr so we add it to the peerstore
		// so LibP2P knows how to contact it
		ha.Peerstore().AddAddr(peerid, targetAddr, pstore.PermanentAddrTTL)

		log.Println("opening stream")
		// make a new stream from host B to host A
		// it should be handled on host A by the handler we set above because
		// we use the same /p2p/1.0.0 protocol
		s, err := ha.NewStream(context.Background(), peerid, "/p2p/1.0.0")
		if err != nil {
			log.Fatalln(err)
		}
		// Create a buffered stream so that read and writes are non blocking.
		rw := bufio.NewReadWriter(bufio.NewReader(s), bufio.NewWriter(s))

		// Create a thread to read and write data.
		go blockchain.WriteData(rw)
		go blockchain.ReadData(rw)

		select {} // hang forever

	}
}
