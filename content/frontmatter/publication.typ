#import "../main-defs.typ": source

#let publication-page() = {
  set text(size: 9pt)
  set par(first-line-indent: 0pt, justify: false, spacing: 0.7em)
  source(2)
  v(18mm)
  [Copyright © 1987 by John Wiley & Sons, Inc.]
  parbreak()
  [All rights reserved. Published simultaneously in Canada.]
  parbreak()
  [Reproduction or translation of any part of this work beyond that permitted by
    Section 107 or 108 of the 1976 United States Copyright Act without the
    permission of the copyright owner is unlawful. Requests for permission or
    further information should be addressed to the Permissions Department, John
    Wiley & Sons, Inc.]
  parbreak()
  strong(emph[Library of Congress Cataloging in Publication Data:])
  parbreak()
  [Curtis, Charles W. \
    Methods of representation theory—with applications to finite groups and
    orders. \
    (Pure and applied mathematics, ISSN 0079-8185) \
    “A Wiley-Interscience publication.” \
    Includes bibliographies and indexes. \
    1. Representations of groups. 2. Finite groups. I. Reiner, Irving.
    II. Title. \
    III. Series: Pure and applied mathematics (John Wiley & Sons) \
    QA171.C85 512′.2 81-7416 \
    ISBN 0-471-18994-4 (v. 1) \
    ISBN 0-471-88871-0 (v. 2)]
  parbreak()
  [Printed in the United States of America]
  parbreak()
  [10 9 8 7 6 5 4 3 2 1]
}

#publication-page()
