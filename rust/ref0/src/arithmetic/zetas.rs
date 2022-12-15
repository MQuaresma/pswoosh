use crate::arithmetic::params::*;
use crate::arithmetic::fq::*;

pub const ZETAS: [Elem; D/2] = [
    [0x0000000000000001, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000],
    [0xbdc2317e5de0c707, 0xc2bd5814ab1beab4, 0xde55ff1daebf3326, 0x00000000003d05f4],
    [0xfaf5d5f27eb7eae4, 0xbf29997f5f4dd3cb, 0xac6bba3bb116c551, 0x00000000000aecc3],
    [0xede95323ff89bee7, 0xfdd27ed5a8c7efa4, 0xba2ff038e47d278d, 0x000000000003904c],
    [0xa696e93ec821b82d, 0x952703e0af7f2a7f, 0xb2ac9a9423ab932d, 0x00000000000ddb20],
    [0xe56b62d423427c4a, 0xf2db7fecb05b750d, 0x500eed5d264652d3, 0x00000000003d9d21],
    [0xb087830d2953d209, 0xfecf6e97f903e51b, 0x5813797152215afb, 0x00000000003b870e],
    [0xb90352676d664df9, 0xe7a5c3f8f303dee0, 0x1315260109e83d04, 0x00000000002b4f27],
    [0x395ea596f97476f2, 0xb9259726a6ffc03e, 0xda69439f8e8dffca, 0x000000000030f604],
    [0xa19d7756c2c7bde6, 0xda75357daddffa89, 0xb370049f8008b2e2, 0x0000000000110481],
    [0x8c1d1b576b761981, 0x187ee33e011d21e4, 0xb3200bffd904060d, 0x00000000001dd543],
    [0x72e3bf2059613c01, 0x720f32ebc531a76f, 0xf584b26859d4c584, 0x00000000000a4050],
    [0xf4c299c7a1d46b2e, 0x148f89c05ad25b48, 0x88b94500aaaa0e24, 0x000000000015dbc5],
    [0x604dae296c2cdabc, 0x7f155a8c68ff3cc1, 0x723a68b9d0709d1e, 0x00000000001bae36],
    [0x4815a6ba275a29b9, 0x540892f71115e446, 0x8ff5a82df41f32fb, 0x00000000003890a5],
    [0x7dee575f664e80f3, 0xd2ef9d9742ab5aca, 0x3efa0982aec970ef, 0x000000000033c66d],
    [0xe8f2db05478d82b2, 0xd32216de310853e4, 0x3d05e1a36aff9130, 0x0000000000393949],
    [0x45c6df7c8ba7fcb5, 0x95b6c4c086dc9d11, 0xdfa3431d9f913882, 0x000000000011700c],
    [0xbcb9f44b355b16d3, 0xb5d192310b8476f4, 0x82404bb2dee20108, 0x000000000007e9d1],
    [0x109bb81c8d5c98cb, 0xaf6578d97313179b, 0x375e5070a2cb75b6, 0x000000000011af6f],
    [0x7e4d00ef9c100d78, 0x7426529a3362e80e, 0x4e3a181efcf69b81, 0x0000000000220729],
    [0x2e6a7625f8c24004, 0x81ceffa474bff2cc, 0x8c0d7d4821e35ed3, 0x00000000000d7166],
    [0xc8b004cf911f69d6, 0x5a373e83197c26d0, 0x269b6fc22e7c2cf4, 0x0000000000398dcc],
    [0x564994567c3ac94c, 0x82e23492fc195843, 0x5e8a8018ec808243, 0x00000000002a4311],
    [0xc3673a5516ec4d2e, 0x8d35f1ae3e22a7a0, 0x1ac4ece88b04da83, 0x00000000002381a2],
    [0xb4030f51ead0b461, 0x51065b41db35e5ce, 0x2adbeb31462ed3ba, 0x00000000003183c0],
    [0x6c9655e3e54c9690, 0xe2574bc08bab2ab4, 0xba96eb7214dbf5db, 0x0000000000243738],
    [0x7918e2b8f47d2d90, 0x2e20b2cc44607790, 0x4c700b05786f788c, 0x00000000003e25fb],
    [0x39b7a99a212f5f84, 0x97f6d311698a2039, 0x9073b53b974a4f1f, 0x00000000001d8955],
    [0xe24db7c171f3417a, 0xd5c57e468bcc521b, 0x2fe475b5aaf84268, 0x00000000000e4fbb],
    [0xc3829e836b232cc4, 0xf4dfb9c1f616f2f5, 0xcc0b838433929294, 0x00000000001f3b97],
    [0xee977c27c6d0e0a2, 0xbeb8b6a0f836310d, 0x867302ea9604337c, 0x0000000000207691],
    [0x2247f6da2476c0e0, 0x54b508bf3c87a6ed, 0x34fea97e491e6e59, 0x000000000022dca6],
    [0x98f75f551a67f07c, 0x2770ff31d057b00a, 0x5a4bb80513161655, 0x00000000003df89b],
    [0xc20855e8a2b94535, 0x2972bb992c6f9c95, 0x8fe41d2c02be8c11, 0x0000000000214f58],
    [0x8e95d202a54ef478, 0x2d5642dac31b1556, 0x49cdbf030b8d0120, 0x000000000001d472],
    [0xaa0c94fb5f9f6486, 0x9139a34d978d6c5e, 0x1d48ab723412afff, 0x00000000003a777e],
    [0x794008c23d079bfe, 0x169ffffccd0b499a, 0x3fe28592ca6bd60a, 0x0000000000231cab],
    [0xc54cdfddd3c7a59f, 0xfa88c938d179b67d, 0x701a7882d6fbd586, 0x00000000000097fd],
    [0xb0a341d84e0d9658, 0x61c77e924aeb321b, 0x4f984cc8843909ef, 0x0000000000163435],
    [0x8502df8a4af7d5a6, 0x8cf0c15bda26184d, 0xb567edc4d0ed5ee1, 0x00000000001be861],
    [0x85a8d7e86f54ac5f, 0xea96b573882e2c8f, 0x7283c32c77e08e40, 0x00000000002fb6a6],
    [0x7cf0ae2231bec80e, 0xfb75fbb24c53e97b, 0x4c14a86d4f3be6d1, 0x0000000000019bcb],
    [0xdc4ccbedd57f7174, 0x081dd055d4b3f97d, 0x706fff6bb46a6596, 0x00000000002fc80c],
    [0xac3da085d6c92612, 0xe1929e7021776011, 0x6fab06dc40fc74b0, 0x0000000000118689],
    [0xd053a45ada7056ef, 0xef589c89a58121b2, 0x7c23bd5eca076c72, 0x00000000002a48d9],
    [0xfb75f3f8d13463e3, 0x966a2c40d8c822be, 0x9dd201f7a5b9f6da, 0x0000000000329171],
    [0x12ce0569cab638c2, 0xf31a101bc0a7435a, 0xfbe9ca846f1636b6, 0x00000000003dabac],
    [0x3ffa73cee07653c5, 0x29115ce14d47481b, 0xe6b3c001225e080e, 0x000000000027fb1e],
    [0xffb9ee1dec93e9b6, 0x241fbb97b4248232, 0x49bec3158440bc72, 0x0000000000199c69],
    [0x0dc2d01ea92212ef, 0x4664b451b184d576, 0xe3fefaa7bbd5e39c, 0x00000000000919cb],
    [0x2b0e547dea65a9d2, 0xe6e125599ebc5869, 0x51306a0cef556d8f, 0x000000000004b26b],
    [0xbcceb2850ffe7e45, 0x3a03841f8e96033e, 0x7d1d08323bfd7be9, 0x00000000001deccd],
    [0x806440661e5e880e, 0xede5c1e5cc40db5b, 0x5656fd6b34b4dab7, 0x00000000003c23fb],
    [0xfa92dc7487c95460, 0x13436cf821d488f3, 0x0f965a2eab9d6aab, 0x000000000019b0d2],
    [0x5a9c19559c1eb23b, 0x0f08fb7f2a123776, 0xa9e99592075b3897, 0x0000000000036a77],
    [0xf2b7e19c6bba71ac, 0x36dfda8978cdd3a9, 0x960706504b68b298, 0x0000000000150c18],
    [0x7e1862c2a6bd70f6, 0xa44c325a224e8580, 0xd1c8e4e1f214b5fc, 0x000000000034fe42],
    [0x4568c1c71c0f1773, 0xa05aa3931276933d, 0x82c879fcdfa4e018, 0x00000000001f4714],
    [0x8963dfc3914871ba, 0x5c14707b25e98a3b, 0x05eb3fc21bd1b0f3, 0x00000000000b53a6],
    [0x1939c1adbb67d593, 0x0d1f075efcf5cbc5, 0x800ae81e2d4bb7b8, 0x0000000000241504],
    [0xaa0b657ba88c576c, 0xeba8acd00fb21e34, 0x95266c7f010cc700, 0x0000000000245dae],
    [0x84279de5a2014699, 0x0e90c9fe848106b1, 0xe0b007a9fe0472ad, 0x000000000033bd2f],
    [0xc2bc96725952f238, 0xdd556d5734908f01, 0xbbf8a6b23f8dce30, 0x00000000002774b4],
    [0xdec5e974f6dd8b42, 0x174ad5ff278b6e78, 0x3e4ba4e039519b17, 0x0000000000007d80],
    [0xe117c8d624872580, 0x4d6021296da2eaa1, 0x8c4148a769d34e6e, 0x0000000000143586],
    [0xdc0d15bb167b3652, 0x3282d54c309d3c6a, 0x13637c06f947a32f, 0x00000000001490bd],
    [0xa60b3b77ab85367d, 0x9c42da09062520fc, 0x2250b7283bef52b3, 0x000000000032cfc0],
    [0x9e022e5b66b1950e, 0x0fd68cc6af8fbdfe, 0x9f99675076d6b115, 0x00000000001d9599],
    [0x89686aae6848321f, 0x7e4068026c43142e, 0x6de95be7fcb42280, 0x000000000039724f],
    [0x4408c7164b5b76ea, 0xb24ff4dd6ad28bd1, 0xc95a91e5e0c61d4b, 0x00000000003e0bbd],
    [0x9676fe8d5e88bdf1, 0xe0e2f6ccc59d2455, 0xe01cdd7eecc493ae, 0x00000000002aff56],
    [0xb1fb5a01b10d32e8, 0x68803c0ac2b2d205, 0x3588d83e8c35debe, 0x00000000001f0c16],
    [0x425f095125c635ff, 0x408941b10b404352, 0x9ee2748c9f315b3b, 0x0000000000387a18],
    [0xbac1632586c2db61, 0xc5652a4a605be75d, 0x8735bcafcdbf9c43, 0x000000000025331f],
    [0x02d9d0f07fd5eafb, 0xf1a89de5606a3b5c, 0x59240a10d64b7026, 0x00000000002258fd],
    [0xbd09d1543c67e505, 0x7fcbfa1e5d07e186, 0xe8a7ffa002e76172, 0x00000000002f6c4b],
    [0xa8fe59c0454122b6, 0x3b8b50e1184d391d, 0x9dab406ed7d26723, 0x00000000000a2ed5],
    [0x97813ab3d8dcf520, 0x43e7db260c0c6c9c, 0xf31c96c7d2e8bada, 0x00000000001309dc],
    [0x72aed164c114e486, 0xc713138f73f7d210, 0x5866708e46ed01b6, 0x0000000000288e6b],
    [0xe69dd599905892ef, 0x802942ebcf9b4d7e, 0x3fdc0a08f46a184d, 0x00000000000d75b7],
    [0x6d68dee0026d68f2, 0x451fadf83a2e2eb9, 0xdf0fcda48de2648d, 0x00000000001d4aa7],
    [0xbeb77e971bbc1318, 0x955dd8ae1c7962d1, 0x5f3ba261fd91632d, 0x000000000031ea98],
    [0x7735397696901776, 0x1f87efe0809c187c, 0x7d38a4258d7dcd07, 0x00000000002099a1],
    [0xa62bdca2acb894a7, 0x382cc25a29e8b13d, 0xd6fd169acad9263d, 0x0000000000277a85],
    [0x2b02095b5f78e8dd, 0x8fc45d4b564d809e, 0xd039015ba34d06c2, 0x00000000002ef341],
    [0x962a6f5d847cc1a2, 0x5489c80695f45dd2, 0xf620064986e73f98, 0x000000000001fddf],
    [0x70a50c5c4612b285, 0x6f9e62ffc7cc3074, 0x083f184e7e7d89c5, 0x00000000001b87a6],
    [0x5db1231993b2e062, 0x9a8c57d878b12a04, 0xf6a50b8b0eeb22f1, 0x000000000034b612],
    [0xc79cbbe0fea22523, 0x6b83f8340686e54d, 0x5b9fbe66ed9ec9d2, 0x00000000002ec510],
    [0x10310493fab08dd7, 0xc05a857f27b423f9, 0x137727d0dff2d3cf, 0x000000000029e977],
    [0x881acb5326576fea, 0x823ff873967b0467, 0x395c3d63108c8815, 0x00000000002ad733],
    [0xb565b62a2f418677, 0xe413dd473d565c29, 0x2339b1f0270803d7, 0x00000000002557e2],
    [0x1954acbe9163c8e7, 0xc05eb5a1171989c3, 0x5b06360a3f163a6f, 0x00000000002ea168],
    [0xb917221fc800593d, 0xac462e0e82527dec, 0x0db436a119b520d8, 0x00000000000a89d0],
    [0x88df88f95ad07a69, 0x6ebf0c90e32783c7, 0x514582cbdcb2319a, 0x000000000039d3d3],
    [0x46405412dca68e2f, 0xe578506b7f0eca25, 0x06e343f07e99807e, 0x000000000032ba2b],
    [0x56501da0dd144215, 0x1f2e901e495c6b50, 0x7589404b898857b7, 0x000000000023d3e4],
    [0xc4251809d9a17921, 0x1a66dc90ad821c03, 0x8ca6fed305cc376f, 0x0000000000151281],
    [0xc45ef328515e71c1, 0x5fee7bdd9c2904a0, 0x6e9f7f1ee7aa99c5, 0x0000000000287f7e],
    [0x6e3696ad5d5e7104, 0x9567524e60e86db4, 0x92281a20a6498a83, 0x0000000000328d2d],
    [0xe5570ec6e9b11d15, 0x01443fb9ce4db781, 0x9f695c6d982c8120, 0x000000000021bbc5],
    [0xddb4edd7afbbe28f, 0x83a385758e80706a, 0x5f440f06f934c060, 0x000000000037c3c6],
    [0x30c50130b6c97426, 0x5f6f6f211f4f1b5d, 0xdcaeee4a94dfdac0, 0x00000000001aeba3],
    [0x12b18d392af13a64, 0x1e669cb9f4a6d3c9, 0xbc51c1cdeb745d53, 0x00000000001e7276],
    [0x876119c3117b6e62, 0x124f47c6ed0b2f65, 0x656c5c2f90ac1c15, 0x000000000019a01a],
    [0x8a1727415b430210, 0xe19148e51598856e, 0x5ac3e0bbabe6bc8b, 0x00000000001e53b0],
    [0x6afe5069a35ba52b, 0xe0eb86f5c12cc3f5, 0x82cb8ba206df3138, 0x000000000005d7df],
    [0xf5af1679d5e387db, 0xa971ae9ae747798b, 0xdcf987d2f751feac, 0x0000000000270b77],
    [0x8984bd1b203d5d9a, 0x048aa504ba76e2be, 0x67a9eb8db1b55f79, 0x000000000035bffe],
    [0x7e2c04ed3ebb8449, 0x38657b7443be4675, 0x0701ab37680a45c8, 0x00000000003b79e2],
    [0x2dcb6279f5f20b2e, 0xc0cc78bf75a16650, 0xd2b0fabc5b5d464e, 0x0000000000207301],
    [0x8ccfd893c25f459c, 0xb05ec5210a6706ca, 0x14344e4c17e55319, 0x0000000000236461],
    [0x4aa4a51244d15e21, 0x92598599213cd58a, 0x89fb857c48607c75, 0x00000000000de94b],
    [0x66e283f2687db6ad, 0x0727bf4cbd668da1, 0xb3e13d0401d1f6ce, 0x0000000000119685],
    [0xa85777309d01cc3c, 0x7d6a8736880e4067, 0x82cc097903dc6b7d, 0x0000000000135603],
    [0x7940fd28040a0fa4, 0x4a8951a1f9e67cc8, 0x1a03b75b778f7666, 0x000000000026ecf3],
    [0x0ab714676ae68596, 0xa098c1be7f56a046, 0x7efc081a21224e17, 0x00000000002c8f0a],
    [0x174d4c5007b06b45, 0x82d56b9705d8d2b8, 0xd31ecf9791db7bfc, 0x000000000001f2cc],
    [0xb2e25c0dfa67c342, 0xa22d0d3027ce3b5b, 0x3dfcb13e62e50860, 0x000000000011f233],
    [0x83ee6920033ec4b7, 0xb7376a641af3efae, 0x75b78db477816798, 0x00000000002ae952],
    [0x09feefa78ee0cc58, 0x5b178b876318b3e0, 0x728edfc0cfe845bc, 0x0000000000197685],
    [0x4270fdf1f406da1a, 0xb04ad8526c249890, 0xf1574377ac07857d, 0x00000000002ee2a9],
    [0x068186019126496c, 0xc2ef717e5b6e9609, 0x395fed8f8bf442bc, 0x000000000014ee40],
    [0x7016ac8ad10bbf4f, 0x84f4d970d394f0ac, 0x4070aa8f9360bb53, 0x00000000000105a8],
    [0x27f991a4d0753063, 0xb2e7aa37c88d7019, 0xb538dff7a1bf9d1e, 0x0000000000123254],
    [0x6c3db234c99c9d14, 0x626111baf3cc58cb, 0xfbbdf0cd11347255, 0x0000000000043042],
    [0xf8af1710d78d1cf8, 0x0d06c841386a8209, 0x3022ba3b626f3ad2, 0x00000000003ec46f]];

pub const ZETAS_INV: [Elem; D/2] = [
    [0x0750e8ef2872e209, 0xf2f937bec7957df6, 0xcfdd45c49d90c52d, 0x0000000000013b90],
    [0x93c24dcb366361ed, 0x9d9eee450c33a734, 0x04420f32eecb8daa, 0x00000000003bcfbd],
    [0xd8066e5b2f8ace9e, 0x4d1855c837728fe6, 0x4ac720085e4062e1, 0x00000000002dcdab],
    [0x8fe953752ef43fb2, 0x7b0b268f2c6b0f53, 0xbf8f55706c9f44ac, 0x00000000003efa57],
    [0xf97e79fe6ed9b595, 0x3d108e81a49169f6, 0xc6a01270740bbd43, 0x00000000002b11bf],
    [0xbd8f020e0bf924e7, 0x4fb527ad93db676f, 0x0ea8bc8853f87a82, 0x0000000000111d56],
    [0xf6011058711f32a9, 0xa4e874789ce74c1f, 0x8d71203f3017ba43, 0x000000000026897a],
    [0x7c1196dffcc13a4a, 0x48c8959be50c1051, 0x8a48724b887e9867, 0x00000000001516ad],
    [0x4d1da3f205983bbf, 0x5dd2f2cfd831c4a4, 0xc2034ec19d1af79f, 0x00000000002e0dcc],
    [0xe8b2b3aff84f93bc, 0x7d2a9468fa272d47, 0x2ce130686e248403, 0x00000000003e0d33],
    [0xf548eb989519796b, 0x5f673e4180a95fb9, 0x8103f7e5deddb1e8, 0x00000000001370f5],
    [0x86bf02d7fbf5ef5d, 0xb576ae5e06198337, 0xe5fc48a488708999, 0x000000000019130c],
    [0x57a888cf62fe32c5, 0x829578c977f1bf98, 0x7d33f686fc239482, 0x00000000002ca9fc],
    [0x991d7c0d97824854, 0xf8d840b34299725e, 0x4c1ec2fbfe2e0931, 0x00000000002e697a],
    [0xb55b5aedbb2ea0e0, 0x6da67a66dec32a75, 0x76047a83b79f838a, 0x00000000003216b4],
    [0x7330276c3da0b965, 0x4fa13adef598f935, 0xebcbb1b3e81aace6, 0x00000000001c9b9e],
    [0xd2349d860a0df3d3, 0x3f3387408a5e99af, 0x2d4f0543a4a2b9b1, 0x00000000001f8cfe],
    [0x81d3fb12c1447ab8, 0xc79a848bbc41b98a, 0xf8fe54c897f5ba37, 0x000000000004861d],
    [0x767b42e4dfc2a167, 0xfb755afb45891d41, 0x985614724e4aa086, 0x00000000000a4001],
    [0x0a50e9862a1c7726, 0x568e516518b88674, 0x2306782d08ae0153, 0x000000000018f488],
    [0x9501af965ca459d6, 0x1f14790a3ed33c0a, 0x7d34745df920cec7, 0x00000000003a2820],
    [0x75e8d8bea4bcfcf1, 0x1e6eb71aea677a91, 0xa53c1f4454194374, 0x000000000021ac4f],
    [0x789ee63cee84909f, 0xedb0b83912f4d09a, 0x9a93a3d06f53e3ea, 0x0000000000265fe5],
    [0xed4e72c6d50ec49d, 0xe19963460b592c36, 0x43ae3e32148ba2ac, 0x0000000000218d89],
    [0xcf3afecf49368adb, 0xa09090dee0b0e4a2, 0x235111b56b20253f, 0x000000000025145c],
    [0x224b122850441c72, 0x7c5c7a8a717f8f95, 0xa0bbf0f906cb3f9f, 0x0000000000083c39],
    [0x1aa8f139164ee1ec, 0xfebbc04631b2487e, 0x6096a39267d37edf, 0x00000000001e443a],
    [0x91c96952a2a18dfd, 0x6a98adb19f17924b, 0x6dd7e5df59b6757c, 0x00000000000d72d2],
    [0x3ba10cd7aea18d40, 0xa011842263d6fb5f, 0x916080e11855663a, 0x0000000000178081],
    [0x3bdae7f6265e85e0, 0xe599236f527de3fc, 0x7359012cfa33c890, 0x00000000002aed7e],
    [0xa9afe25f22ebbcec, 0xe0d16fe1b6a394af, 0x8a76bfb47677a848, 0x00000000001c2c1b],
    [0xb9bfabed235970d2, 0x1a87af9480f135da, 0xf91cbc0f81667f81, 0x00000000000d45d4],
    [0x77207706a52f8498, 0x9140f36f1cd87c38, 0xaeba7d34234dce65, 0x0000000000062c2c],
    [0x46e8dde037ffa5c4, 0x53b9d1f17dad8213, 0xf24bc95ee64adf27, 0x000000000035762f],
    [0xe6ab53416e9c361a, 0x3fa14a5ee8e6763c, 0xa4f9c9f5c0e9c590, 0x0000000000115e97],
    [0x4a9a49d5d0be788a, 0x1bec22b8c2a9a3d6, 0xdcc64e0fd8f7fc28, 0x00000000001aa81d],
    [0x77e534acd9a88f17, 0x7dc0078c6984fb98, 0xc6a3c29cef7377ea, 0x00000000001528cc],
    [0xefcefb6c054f712a, 0x3fa57a80d84bdc06, 0xec88d82f200d2c30, 0x0000000000161688],
    [0x3863441f015dd9de, 0x947c07cbf9791ab2, 0xa46041991261362d, 0x0000000000113aef],
    [0xa24edce66c4d1e9f, 0x6573a827874ed5fb, 0x095af474f114dd0e, 0x00000000000b49ed],
    [0x8f5af3a3b9ed4c7c, 0x90619d003833cf8b, 0xf7c0e7b18182763a, 0x0000000000247859],
    [0x69d590a27b833d5f, 0xab7637f96a0ba22d, 0x09dff9b67918c067, 0x00000000003e0220],
    [0xd4fdf6a4a0871624, 0x703ba2b4a9b27f61, 0x2fc6fea45cb2f93d, 0x0000000000110cbe],
    [0x59d4235d53476a5a, 0xc7d33da5d6174ec2, 0x2902e9653526d9c2, 0x000000000018857a],
    [0x88cac689696fe78b, 0xe078101f7f63e783, 0x82c75bda728232f8, 0x00000000001f665e],
    [0x41488168e443ebe9, 0x6aa22751e3869d2e, 0xa0c45d9e026e9cd2, 0x00000000000e1567],
    [0x9297211ffd92960f, 0xbae05207c5d1d146, 0x20f0325b721d9b72, 0x000000000022b558],
    [0x19622a666fa76c12, 0x7fd6bd143064b281, 0xc023f5f70b95e7b2, 0x0000000000328a48],
    [0x8d512e9b3eeb1a7b, 0x38ecec708c082def, 0xa7998f71b912fe49, 0x0000000000177194],
    [0x687ec54c272309e1, 0xbc1824d9f3f39363, 0x0ce369382d174525, 0x00000000002cf623],
    [0x5701a63fbabedc4b, 0xc474af1ee7b2c6e2, 0x6254bf91282d98dc, 0x000000000035d12a],
    [0x42f62eabc39819fc, 0x803405e1a2f81e79, 0x1758005ffd189e8d, 0x00000000001093b4],
    [0xfd262f0f802a1406, 0x0e57621a9f95c4a3, 0xa6dbf5ef29b48fd9, 0x00000000001da702],
    [0x453e9cda793d23a0, 0x3a9ad5b59fa418a2, 0x78ca4350324063bc, 0x00000000001acce0],
    [0xbda0f6aeda39c902, 0xbf76be4ef4bfbcad, 0x611d8b7360cea4c4, 0x00000000000785e7],
    [0x4e04a5fe4ef2cc19, 0x977fc3f53d4d2dfa, 0xca7727c173ca2141, 0x000000000020f3e9],
    [0x69890172a1774110, 0x1f1d09333a62dbaa, 0x1fe32281133b6c51, 0x00000000001500a9],
    [0xbbf738e9b4a48817, 0x4db00b22952d742e, 0x36a56e1a1f39e2b4, 0x000000000001f442],
    [0x7697955197b7cce2, 0x81bf97fd93bcebd1, 0x9216a418034bdd7f, 0x0000000000068db0],
    [0x61fdd1a4994e69f3, 0xf029733950704201, 0x606698af89294eea, 0x0000000000226a66],
    [0x59f4c488547ac884, 0x63bd25f6f9dadf03, 0xddaf48d7c410ad4c, 0x00000000000d303f],
    [0x23f2ea44e984c8af, 0xcd7d2ab3cf62c395, 0xec9c83f906b85cd0, 0x00000000002b6f42],
    [0x1ee83729db78d981, 0xb29fded6925d155e, 0x73beb758962cb191, 0x00000000002bca79],
    [0x213a168b092273bf, 0xe8b52a00d8749187, 0xc1b45b1fc6ae64e8, 0x00000000003f827f],
    [0x3d43698da6ad0cc9, 0x22aa92a8cb6f70fe, 0x4407594dc07231cf, 0x0000000000188b4b],
    [0x7bd8621a5dfeb868, 0xf16f36017b7ef94e, 0x1f4ff85601fb8d52, 0x00000000000c42d0],
    [0x55f49a845773a795, 0x1457532ff04de1cb, 0x6ad99380fef338ff, 0x00000000001ba251],
    [0xe6c63e524498296e, 0xf2e0f8a1030a343a, 0x7ff517e1d2b44847, 0x00000000001beafb],
    [0x769c203c6eb78d47, 0xa3eb8f84da1675c4, 0xfa14c03de42e4f0c, 0x000000000034ac59],
    [0xba973e38e3f0e78e, 0x5fa55c6ced896cc2, 0x7d378603205b1fe7, 0x000000000020b8eb],
    [0x81e79d3d59428e0b, 0x5bb3cda5ddb17a7f, 0x2e371b1e0deb4a03, 0x00000000000b01bd],
    [0x0d481e6394458d55, 0xc920257687322c56, 0x69f8f9afb4974d67, 0x00000000002af3e7],
    [0xa563e6aa63e14cc6, 0xf0f70480d5edc889, 0x56166a6df8a4c768, 0x00000000003c9588],
    [0x056d238b7836aaa1, 0xecbc9307de2b770c, 0xf069a5d154629554, 0x0000000000264f2d],
    [0x7f9bbf99e1a176f3, 0x121a3e1a33bf24a4, 0xa9a90294cb4b2548, 0x000000000003dc04],
    [0x43314d7af00180bc, 0xc5fc7be07169fcc1, 0x82e2f7cdc4028416, 0x0000000000221332],
    [0xd4f1ab82159a552f, 0x191edaa66143a796, 0xaecf95f310aa9270, 0x00000000003b4d94],
    [0xf23d2fe156ddec12, 0xb99b4bae4e7b2a89, 0x1c010558442a1c63, 0x000000000036e634],
    [0x004611e2136c154b, 0xdbe044684bdb7dcd, 0xb6413cea7bbf438d, 0x0000000000266396],
    [0xc0058c311f89ab3c, 0xd6eea31eb2b8b7e4, 0x194c3ffedda1f7f1, 0x00000000001804e1],
    [0xed31fa963549c63f, 0x0ce5efe43f58bca5, 0x0416357b90e9c949, 0x0000000000025453],
    [0x048a0c072ecb9b1e, 0x6995d3bf2737dd41, 0x622dfe085a460925, 0x00000000000d6e8e],
    [0x2fac5ba5258fa812, 0x10a763765a7ede4d, 0x83dc42a135f8938d, 0x000000000015b726],
    [0x53c25f7a2936d8ef, 0x1e6d618fde889fee, 0x9054f923bf038b4f, 0x00000000002e7976],
    [0x23b334122a808d8d, 0xf7e22faa2b4c0682, 0x8f9000944b959a69, 0x00000000001037f3],
    [0x830f51ddce4136f3, 0x048a044db3ac1684, 0xb3eb5792b0c4192e, 0x00000000003e6434],
    [0x7a57281790ab52a2, 0x15694a8c77d1d370, 0x8d7c3cd3881f71bf, 0x0000000000104959],
    [0x7afd2075b508295b, 0x730f3ea425d9e7b2, 0x4a98123b2f12a11e, 0x000000000024179e],
    [0x4f5cbe27b1f268a9, 0x9e38816db514cde4, 0xb067b3377bc6f610, 0x000000000029cbca],
    [0x3ab320222c385962, 0x057736c72e864982, 0x8fe5877d29042a79, 0x00000000003f6802],
    [0x86bff73dc2f86303, 0xe960000332f4b665, 0xc01d7a6d359429f5, 0x00000000001ce354],
    [0x55f36b04a0609a7b, 0x6ec65cb2687293a1, 0xe2b7548dcbed5000, 0x0000000000058881],
    [0x716a2dfd5ab10a89, 0xd2a9bd253ce4eaa9, 0xb63240fcf472fedf, 0x00000000003e2b8d],
    [0x3df7aa175d46b9cc, 0xd68d4466d390636a, 0x701be2d3fd4173ee, 0x00000000001eb0a7],
    [0x6708a0aae5980e85, 0xd88f00ce2fa84ff5, 0xa5b447faece9e9aa, 0x0000000000020764],
    [0xddb80925db893e21, 0xab4af740c3785912, 0xcb015681b6e191a6, 0x00000000001d2359],
    [0x116883d8392f1e5f, 0x4147495f07c9cef2, 0x798cfd1569fbcc83, 0x00000000001f896e],
    [0x3c7d617c94dcd23d, 0x0b20463e09e90d0a, 0x33f47c7bcc6d6d6b, 0x000000000020c468],
    [0x1db2483e8e0cbd87, 0x2a3a81b97433ade4, 0xd01b8a4a5507bd97, 0x000000000031b044],
    [0xc6485665ded09f7d, 0x68092cee9675dfc6, 0x6f8c4ac468b5b0e0, 0x00000000002276aa],
    [0x86e71d470b82d171, 0xd1df4d33bb9f886f, 0xb38ff4fa87908773, 0x000000000001da04],
    [0x9369aa1c1ab36871, 0x1da8b43f7454d54b, 0x4569148deb240a24, 0x00000000001bc8c7],
    [0x4bfcf0ae152f4aa0, 0xaef9a4be24ca1a31, 0xd52414ceb9d12c45, 0x00000000000e7c3f],
    [0x3c98c5aae913b1d3, 0x72ca0e51c1dd585f, 0xe53b131774fb257c, 0x00000000001c7e5d],
    [0xa9b66ba983c535b5, 0x7d1dcb6d03e6a7bc, 0xa1757fe7137f7dbc, 0x000000000015bcee],
    [0x374ffb306ee0952b, 0xa5c8c17ce683d92f, 0xd964903dd183d30b, 0x0000000000067233],
    [0xd19589da073dbefd, 0x7e31005b8b400d33, 0x73f282b7de1ca12c, 0x0000000000328e99],
    [0x81b2ff1063eff189, 0x8bd9ad65cc9d17f1, 0xb1c5e7e10309647e, 0x00000000001df8d6],
    [0xef6447e372a36636, 0x509a87268cece864, 0xc8a1af8f5d348a49, 0x00000000002e5090],
    [0x43460bb4caa4e82e, 0x4a2e6dcef47b890b, 0x7dbfb44d211dfef7, 0x000000000038162e],
    [0xba3920837458024c, 0x6a493b3f792362ee, 0x205cbce2606ec77d, 0x00000000002e8ff3],
    [0x170d24fab8727c4f, 0x2cdde921cef7ac1b, 0xc2fa1e5c95006ecf, 0x000000000006c6b6],
    [0x8211a8a099b17e0e, 0x2d106268bd54a535, 0xc105f67d51368f10, 0x00000000000c3992],
    [0xb7ea5945d8a5d548, 0xabf76d08eeea1bb9, 0x700a57d20be0cd04, 0x0000000000076f5a],
    [0x9fb251d693d32445, 0x80eaa5739700c33e, 0x8dc597462f8f62e1, 0x00000000002451c9],
    [0x0b3d66385e2b93d3, 0xeb70763fa52da4b7, 0x7746baff5555f1db, 0x00000000002a243a],
    [0x8d1c40dfa69ec300, 0x8df0cd143ace5890, 0x0a7b4d97a62b3a7b, 0x000000000035bfaf],
    [0x73e2e4a89489e580, 0xe7811cc1fee2de1b, 0x4cdff40026fbf9f2, 0x0000000000222abc],
    [0x5e6288a93d38411b, 0x258aca8252200576, 0x4c8ffb607ff74d1d, 0x00000000002efb7e],
    [0xc6a15a69068b880f, 0x46da68d959003fc1, 0x2596bc6071720035, 0x00000000000f09fb],
    [0x46fcad989299b108, 0x185a3c070cfc211f, 0xecead9fef617c2fb, 0x000000000014b0d8],
    [0x4f787cf2d6ac2cf8, 0x0130916806fc1ae4, 0xa7ec868eaddea504, 0x00000000000478f1],
    [0x1a949d2bdcbd82b7, 0x0d2480134fa48af2, 0xaff112a2d9b9ad2c, 0x00000000000262de],
    [0x596916c137de46d4, 0x6ad8fc1f5080d580, 0x4d53656bdc546cd2, 0x00000000003224df],
    [0x1216acdc0076401a, 0x022d812a5738105b, 0x45d00fc71b82d872, 0x00000000003c6fb3],
    [0x050a2a0d8148141d, 0x40d66680a0b22c34, 0x539445c44ee93aae, 0x000000000035133c],
    [0x423dce81a21f37fa, 0x3d42a7eb54e4154b, 0x21aa00e25140ccd9, 0x000000000002fa0b],
    [0xffffffffffffff03, 0xffffffffffffffff, 0xffffffffffffffff, 0x00000000003f7fff]];
